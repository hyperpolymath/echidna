# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

"""
    api/gnn_endpoint.jl

GNN inference endpoints for the ECHIDNA ML API server.

Accepts proof graphs from the Rust core (serialised by src/rust/gnn/client.rs)
and runs GNN-based premise ranking using the neural_solver.jl pipeline.

Endpoints:
- POST /gnn/rank   — Rank premises in a proof graph
- POST /gnn/embed  — Return node embeddings for a proof graph
- GET  /gnn/health — Check GNN model availability

Protocol: JSON request/response matching the GnnRankRequest/GnnRankResponse
structs in src/rust/gnn/client.rs.
"""

using HTTP
using JSON3
using Flux
using GraphNeuralNetworks
using Graphs
using SimpleWeightedGraphs
using Statistics
using LinearAlgebra

# Reference to global GNN model (loaded at server startup)
const GNN_MODEL = Ref{Any}(nothing)
const GNN_VOCAB = Ref{Any}(nothing)

# Per-(prover, domain) success-rate weights pushed from Rust via
# POST /training/update.  Format: weights[prover_name][domain] = success_rate.
# Used to modulate premise scores in rank_with_gnn when domain_hints present.
const PROVER_DOMAIN_WEIGHTS = Ref{Dict{String,Dict{String,Float64}}}(Dict())

# Running total of training records received since server start.
const TOTAL_TRAINING_RECORDS = Ref{Int}(0)

"""
    load_gnn_model(models_dir::String)

Load the GNN premise ranker model from disk.
Falls back to creating a fresh (untrained) model if no checkpoint exists.
"""
function load_gnn_model(models_dir::String)
    model_path = joinpath(models_dir, "neural", "gnn_ranker")

    if isdir(model_path)
        @info "Loading GNN model from $model_path"
        try
            solver = load_solver(model_path)
            GNN_MODEL[] = solver
            @info "GNN model loaded successfully"
            return true
        catch e
            @warn "Failed to load GNN model: $e"
        end
    end

    @info "No trained GNN model found — creating fresh model for inference"
    # Create a minimal model with default configuration for the endpoint
    # to respond (scores will be random until training completes)
    GNN_MODEL[] = nothing
    return false
end

"""
    parse_proof_graph(body)

Parse a GnnRankRequest JSON body into internal graph structures.
Returns (graph, goal_idx, premise_indices, node_labels) or throws on error.
"""
function parse_proof_graph(body)
    graph_data = body[:graph]

    num_nodes = graph_data[:num_nodes]
    num_edges = graph_data[:num_edges]
    edge_src = Int.(graph_data[:edge_src]) .+ 1   # 0-indexed -> 1-indexed
    edge_dst = Int.(graph_data[:edge_dst]) .+ 1
    edge_weights = Float32.(graph_data[:edge_weights])
    node_features_flat = Float32.(graph_data[:node_features])
    feature_dim = Int(graph_data[:feature_dim])
    node_labels = String.(graph_data[:node_labels])
    goal_idx = haskey(graph_data, :goal_node_idx) && graph_data[:goal_node_idx] !== nothing ?
        Int(graph_data[:goal_node_idx]) + 1 : nothing
    premise_indices = haskey(graph_data, :premise_node_indices) ?
        Int.(graph_data[:premise_node_indices]) .+ 1 : Int[]

    # Reconstruct node feature matrix: (feature_dim, num_nodes)
    node_features = reshape(node_features_flat, feature_dim, num_nodes)

    # Build weighted directed graph
    g = SimpleWeightedDiGraph(num_nodes)
    for i in 1:num_edges
        add_edge!(g, edge_src[i], edge_dst[i], edge_weights[i])
    end

    return (g, node_features, goal_idx, premise_indices, node_labels, feature_dim)
end

"""
    rank_with_gnn(g, node_features, goal_idx, premise_indices, config, domain_hints)

Run GNN message passing + cross-attention scoring on the parsed graph.
If a trained model is available, use it. Otherwise, use cosine similarity
between the goal and premise node features as a fallback.

When `domain_hints` is non-empty and `PROVER_DOMAIN_WEIGHTS` has been
populated by prior `/training/update` calls, premise scores are modulated
by the aggregate domain confidence from accumulated proof outcomes.
"""
function rank_with_gnn(g, node_features, goal_idx, premise_indices, config, domain_hints=String[])
    model = GNN_MODEL[]

    if model !== nothing
        scores, indices = rank_with_trained_model(model, g, node_features, goal_idx, premise_indices)
    else
        # Fallback: cosine similarity between goal and premise features
        scores, indices = rank_with_cosine(node_features, goal_idx, premise_indices)
    end

    # Apply accumulated training weights when the caller provided domain hints.
    # This is a no-op until /training/update has been called at least once
    # and the rank request includes non-empty domain_hints.
    if !isempty(domain_hints) && !isempty(PROVER_DOMAIN_WEIGHTS[])
        scores = apply_domain_weights(scores, domain_hints)
    end

    return (scores, indices)
end

"""
    apply_domain_weights(scores, domain_hints)

Scale premise scores by the mean success rate across all provers for the
requested domain aspects.  Uses a `[0.5, 1.0]` range so that even low-
confidence domains retain half the base score rather than collapsing to zero.

When no training evidence exists for the requested domains, scores are
returned unchanged.
"""
function apply_domain_weights(scores::Vector{Float32}, domain_hints::Vector{String})
    weights = PROVER_DOMAIN_WEIGHTS[]
    domain_rates = Float64[]
    for domain in domain_hints
        for (_, prover_weights) in weights
            if haskey(prover_weights, domain)
                push!(domain_rates, prover_weights[domain])
            end
        end
    end
    isempty(domain_rates) && return scores
    mean_confidence = Statistics.mean(domain_rates)
    scale = Float32(0.5 + 0.5 * mean_confidence)
    return scores .* scale
end

"""
    handle_training_update(req::HTTP.Request)

POST /training/update — Receive proof-outcome statistics from the Rust server
and update per-(prover, domain) success-rate weights used to modulate premise
ranking scores.

Payload: `{ "records": [{ "prover", "domain", "attempts", "successes",
                           "timeouts", "failures", "mean_time_ms", "success_rate" }] }`

The Rust `StatisticsTracker` is authoritative; Julia simply mirrors it so that
the GNN ranking layer can incorporate proof-outcome evidence without a round-trip.
"""
function handle_training_update(req::HTTP.Request)
    try
        body = JSON3.read(String(req.body))
        records = get(body, :records, [])

        weights = PROVER_DOMAIN_WEIGHTS[]
        n = 0
        for rec in records
            prover = string(get(rec, :prover, "Unknown"))
            domain = string(get(rec, :domain, "unspecified"))
            rate   = Float64(get(rec, :success_rate, 0.0))
            if !haskey(weights, prover)
                weights[prover] = Dict{String,Float64}()
            end
            weights[prover][domain] = rate
            n += 1
        end
        PROVER_DOMAIN_WEIGHTS[] = weights
        TOTAL_TRAINING_RECORDS[] += n

        @info "Training update: $n records (total=$(TOTAL_TRAINING_RECORDS[]))"

        return HTTP.Response(200, JSON3.write(Dict(
            "status"          => "ok",
            "records_received" => n,
            "total_records"   => TOTAL_TRAINING_RECORDS[],
            "weights_updated" => n > 0
        )))
    catch e
        @error "Training update failed" exception=(e, catch_backtrace())
        return HTTP.Response(500, JSON3.write(Dict(
            "status" => "error",
            "error"  => string(e)
        )))
    end
end

"""
    rank_with_cosine(node_features, goal_idx, premise_indices)

Fallback ranking using cosine similarity between the goal node
and each premise node in the feature space.
"""
function rank_with_cosine(node_features, goal_idx, premise_indices)
    if goal_idx === nothing || isempty(premise_indices)
        return (zeros(Float32, length(premise_indices)), premise_indices)
    end

    goal_feat = node_features[:, goal_idx]
    goal_norm = norm(goal_feat)

    scores = Float32[]
    for pidx in premise_indices
        premise_feat = node_features[:, pidx]
        premise_norm = norm(premise_feat)

        if goal_norm > 1f-10 && premise_norm > 1f-10
            sim = dot(goal_feat, premise_feat) / (goal_norm * premise_norm)
            # Normalise from [-1, 1] to [0, 1]
            push!(scores, (sim + 1f0) / 2f0)
        else
            push!(scores, 0f0)
        end
    end

    return (scores, premise_indices)
end

"""
    rank_with_trained_model(model, g, node_features, goal_idx, premise_indices)

Rank premises using the trained GNN model (PremiseRanker from neural_solver.jl).
"""
function rank_with_trained_model(model, g, node_features, goal_idx, premise_indices)
    # Build TheoremGraph from parsed data
    node_types = fill(:premise, size(node_features, 2))
    if goal_idx !== nothing
        node_types[goal_idx] = :goal
    end
    node_names = ["node_$i" for i in 1:size(node_features, 2)]

    # Create TheoremGraph compatible with the PremiseRanker
    theorem_graph = TheoremGraph(
        g, node_features, node_types, node_names,
        AGDA  # Default prover; actual prover is encoded in features
    )

    # Run the ranker
    scores = model.premise_ranker(theorem_graph)

    # Extract scores for premise nodes only
    premise_scores = Float32[scores[min(i, length(scores))] for i in premise_indices]

    return (premise_scores, premise_indices)
end

"""
    handle_gnn_rank(req::HTTP.Request)

POST /gnn/rank — Rank premises in a proof graph using the GNN.
"""
function handle_gnn_rank(req::HTTP.Request)
    start_time = time()

    try
        body = JSON3.read(String(req.body))

        # Parse the proof graph
        (g, node_features, goal_idx, premise_indices, node_labels, feature_dim) =
            parse_proof_graph(body)

        top_k = get(body, :top_k, 20)
        min_score = get(body, :min_score, 0.05)
        include_embeddings = get(body, :include_embeddings, false)
        domain_hints = String.(get(body, :domain_hints, String[]))

        # Run GNN ranking; domain_hints allow weight-guided score modulation
        # when /training/update has populated PROVER_DOMAIN_WEIGHTS.
        (scores, indices) = rank_with_gnn(
            g, node_features, goal_idx, premise_indices,
            get(body, :config, nothing),
            domain_hints
        )

        # Sort by score (descending)
        sorted_order = sortperm(scores, rev=true)
        sorted_scores = scores[sorted_order]
        sorted_indices = indices[sorted_order]

        # Filter by min_score and top_k
        filtered_mask = sorted_scores .>= min_score
        sorted_scores = sorted_scores[filtered_mask]
        sorted_indices = sorted_indices[filtered_mask]
        sorted_scores = sorted_scores[1:min(top_k, length(sorted_scores))]
        sorted_indices = sorted_indices[1:min(top_k, length(sorted_indices))]

        # Get premise names
        premise_names = [node_labels[idx] for idx in sorted_indices]

        elapsed_ms = Float32((time() - start_time) * 1000)

        response = Dict(
            "success" => true,
            "scores" => sorted_scores,
            "premise_names" => premise_names,
            "inference_time_ms" => elapsed_ms
        )

        # Optionally include node embeddings
        if include_embeddings
            embeddings = [Float32.(node_features[:, i]) for i in 1:size(node_features, 2)]
            response["embeddings"] = embeddings
        end

        return HTTP.Response(200, JSON3.write(response))

    catch e
        @error "GNN rank request failed" exception=(e, catch_backtrace())
        return HTTP.Response(500, JSON3.write(Dict(
            "success" => false,
            "error" => string(e),
            "scores" => Float32[],
            "premise_names" => String[],
            "inference_time_ms" => 0f0
        )))
    end
end

"""
    handle_gnn_health(req::HTTP.Request)

GET /gnn/health — Check GNN model availability.
"""
function handle_gnn_health(req::HTTP.Request)
    model_loaded = GNN_MODEL[] !== nothing

    response = Dict(
        "status" => "ok",
        "gnn_model_loaded" => model_loaded,
        "num_gnn_layers" => model_loaded ? 4 : 0,
        "service" => "echidna-gnn",
        "version" => "2.1.0"
    )

    return HTTP.Response(200, JSON3.write(response))
end

"""
    register_gnn_routes!(router)

Register GNN endpoints with the API router.
Call this from the main api_server.jl to enable GNN functionality.
"""
function register_gnn_routes!(existing_handler)
    @info "Registering GNN endpoints:"
    @info "  POST /gnn/rank        — Rank premises via GNN"
    @info "  GET  /gnn/health      — GNN model status"
    @info "  POST /training/update — Receive proof-outcome stats from Rust"

    function combined_handler(req::HTTP.Request)
        if req.target == "/gnn/rank" && req.method == "POST"
            return handle_gnn_rank(req)
        elseif req.target == "/gnn/health"
            return handle_gnn_health(req)
        elseif req.target == "/training/update" && req.method == "POST"
            return handle_training_update(req)
        else
            return existing_handler(req)
        end
    end

    return combined_handler
end
