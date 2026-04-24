# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# api/server.jl — HTTP API server for neural premise selection.
# Uses HTTP.jl directly (no Oxygen macro routing — compatible with module includes).
#
# Endpoints:
#   GET  /health        — Health check
#   GET  /metrics       — Server metrics
#   GET  /provers       — List supported provers
#   POST /predict       — Single premise prediction
#   POST /suggest       — Interactive tactic suggestion (Rust server calls this)

using HTTP
using JSON3
using Logging
using Dates
using Statistics

# ============================================================================
# Server State
# ============================================================================

mutable struct ServerState
    solver::Union{Nothing, NeuralSolver}
    vocabulary::Union{Nothing, ProverVocabulary}
    cache::InferenceCache
    request_count::Int
    start_time::DateTime
    model_path::String
    port::Int
    host::String
end

const SERVER_STATE = Ref{ServerState}()

function init_server_state(model_path::String; cache_size::Int=1000,
                           port::Int=8090, host::String="0.0.0.0")
    @info "Loading model from $model_path"
    solver = load_solver(model_path)
    vocabulary = solver.vocabulary
    cache = InferenceCache(cache_size)

    state = ServerState(solver, vocabulary, cache, 0, now(), model_path, port, host)
    SERVER_STATE[] = state
    @info "Server state initialized"
    return state
end

function get_state()
    isassigned(SERVER_STATE) || error("Server not initialized")
    return SERVER_STATE[]
end

# ============================================================================
# Request/Response types
# ============================================================================

function parse_prover(prover_str::String)
    prover_map = Dict(
        "agda" => AGDA, "coq" => COQ, "rocq" => ROCQ, "lean" => LEAN,
        "isabelle" => ISABELLE, "z3" => Z3, "cvc5" => CVC5,
        "metamath" => METAMATH, "hol_light" => HOL_LIGHT, "hollight" => HOL_LIGHT,
        "mizar" => MIZAR, "pvs" => PVS, "acl2" => ACL2, "hol4" => HOL4,
        "idris2" => IDRIS2, "vampire" => VAMPIRE, "eprover" => EPROVER,
        "spass" => SPASS, "alt-ergo" => ALT_ERGO,
    )
    prover_lower = lowercase(prover_str)
    haskey(prover_map, prover_lower) || error("Unknown prover: $prover_str")
    return prover_map[prover_lower]
end

# ============================================================================
# Route handler
# ============================================================================

function handle_request(req::HTTP.Request)
    path = HTTP.URI(req.target).path
    method = req.method

    try
        if method == "GET" && path == "/health"
            return handle_health()
        elseif method == "GET" && path == "/metrics"
            return handle_metrics()
        elseif method == "GET" && path == "/provers"
            return handle_provers()
        elseif method == "POST" && path == "/predict"
            return handle_predict(req)
        elseif method == "POST" && path == "/suggest"
            return handle_suggest(req)
        else
            return HTTP.Response(404, JSON3.write(Dict("error" => "Not found")))
        end
    catch e
        @error "Request error" path exception=(e, catch_backtrace())
        return HTTP.Response(500, JSON3.write(Dict(
            "success" => false,
            "error" => string(e)
        )))
    end
end

function handle_health()
    state = get_state()
    uptime = (now() - state.start_time).value / 1000
    body = Dict(
        "status" => "healthy",
        "model_loaded" => state.solver !== nothing,
        "uptime_seconds" => uptime,
        "request_count" => state.request_count,
        "cache" => Dict(
            "hits" => state.cache.hits,
            "misses" => state.cache.misses,
            "size" => length(state.cache.cache)
        )
    )
    return HTTP.Response(200, JSON3.write(body))
end

function handle_metrics()
    state = get_state()
    uptime = (now() - state.start_time).value / 1000
    body = Dict(
        "uptime_seconds" => uptime,
        "total_requests" => state.request_count,
        "requests_per_second" => state.request_count / max(uptime, 1),
        "cache_hits" => state.cache.hits,
        "cache_misses" => state.cache.misses,
        "model_path" => state.model_path,
        "gpu_available" => CUDA.functional(),
    )
    return HTTP.Response(200, JSON3.write(body))
end

function handle_provers()
    body = Dict(
        "supported" => [string(p) for p in instances(ProverType)],
        "total" => length(instances(ProverType))
    )
    return HTTP.Response(200, JSON3.write(body))
end

function handle_predict(req::HTTP.Request)
    state = get_state()
    state.request_count += 1

    body = try
        JSON3.read(String(req.body))
    catch e
        return HTTP.Response(400, JSON3.write(Dict("error" => "Invalid JSON: $(e)")))
    end

    prover = parse_prover(get(body, :prover, "lean"))
    goal_text = get(body, :goal, "")
    context = String.(get(body, :context, String[]))
    hypotheses = String.(get(body, :hypotheses, String[]))
    top_k = get(body, :top_k, 10)
    min_conf = Float32(get(body, :min_confidence, 0.1))

    # Build proof state
    proof_state = ProofState(prover, goal_text, context, hypotheses, String[], 0, Dict{String,Any}())

    # Build available premises from request
    raw_premises = get(body, :available_premises, Dict{String,Any}[])
    premises = Premise[]
    for p in raw_premises
        push!(premises, Premise(
            get(p, :name, ""),
            get(p, :statement, ""),
            prover, nothing,
            Float32(get(p, :frequency_score, 0.0)),
            Float32(get(p, :relevance_score, 0.0))
        ))
    end

    # Run inference
    t0 = time()
    if !isempty(premises) && state.solver !== nothing
        ranking = predict_premises(state.solver, proof_state, premises;
                                    top_k=top_k, min_confidence=min_conf,
                                    use_cache=true, cache=state.cache)
        inference_ms = (time() - t0) * 1000

        result_premises = [Dict(
            "name" => p.name, "statement" => p.statement,
            "score" => s, "frequency_score" => p.frequency_score
        ) for (p, s) in zip(ranking.premises, ranking.scores)]

        response = Dict(
            "success" => true,
            "premises" => result_premises,
            "scores" => ranking.scores,
            "confidence" => ranking.confidence,
            "prover" => string(prover),
            "cached" => false,
            "inference_time_ms" => inference_ms
        )
    else
        response = Dict(
            "success" => true,
            "premises" => Dict{String,Any}[],
            "scores" => Float32[],
            "confidence" => 0.0f0,
            "prover" => string(prover),
            "cached" => false,
            "inference_time_ms" => 0.0
        )
    end

    return HTTP.Response(200, JSON3.write(response))
end

function handle_suggest(req::HTTP.Request)
    # The Rust server calls POST /suggest with { goal, prover, top_k }
    state = get_state()
    state.request_count += 1

    body = try
        JSON3.read(String(req.body))
    catch e
        return HTTP.Response(400, JSON3.write(Dict("error" => "Invalid JSON: $(e)")))
    end
    goal_text = get(body, :goal, "")
    prover_str = get(body, :prover, "lean")
    top_k = get(body, :top_k, 5)

    prover = parse_prover(prover_str)

    # Build a simple suggestion response
    # With a trained model this calls suggest_next_step; without, return heuristic suggestions
    suggestions = Dict{String,Any}[]

    if state.solver !== nothing
        proof_state = ProofState(prover, goal_text, String[], String[], String[], 0, Dict{String,Any}())
        # Use basic tactic suggestions based on prover
        common_tactics = if prover in (LEAN,)
            ["rfl", "simp", "ring", "omega", "exact", "apply", "intro", "cases", "induction", "norm_num"]
        elseif prover in (COQ, ROCQ)
            ["reflexivity", "simpl", "auto", "intros", "apply", "rewrite", "induction", "destruct", "unfold", "omega"]
        elseif prover in (Z3, CVC5)
            ["check-sat", "simplify", "propagate-values", "solve-eqs", "elim-uncnstr"]
        else
            ["auto", "apply", "intro", "rewrite", "simp"]
        end

        for (i, tac) in enumerate(common_tactics[1:min(top_k, length(common_tactics))])
            push!(suggestions, Dict(
                "tactic" => tac,
                "confidence" => Float32(1.0 - 0.05 * i),
                "premises" => String[]
            ))
        end
    end

    response = Dict(
        "success" => true,
        "suggestions" => suggestions
    )

    return HTTP.Response(200, JSON3.write(response))
end

# ============================================================================
# Server lifecycle
# ============================================================================

function start_api_server(model_path::String;
                          port::Int=8090, host::String="0.0.0.0",
                          cache_size::Int=1000, async::Bool=false)
    @info "Starting ECHIDNA Neural Solver API"
    @info "Model: $model_path | Host: $host:$port"

    init_server_state(model_path; cache_size=cache_size, port=port, host=host)

    # Wire the GNN endpoint into the trained solver so /gnn/rank uses it
    # instead of falling back to cosine similarity.  The solver loaded by
    # `init_server_state` is a full NeuralSolver (text_encoder + premise_ranker);
    # publish it as the GNN model and combine the route table.
    GNN_MODEL[] = SERVER_STATE[].solver
    GNN_VOCAB[] = SERVER_STATE[].vocabulary
    @info "GNN endpoint wired to trained solver at $model_path"

    @info "Endpoints:"
    @info "  GET  /health"
    @info "  GET  /metrics"
    @info "  GET  /provers"
    @info "  POST /predict"
    @info "  POST /suggest"
    @info "  POST /gnn/rank"
    @info "  GET  /gnn/health"

    combined = register_gnn_routes!(handle_request)
    server = HTTP.serve(combined, host, port)
    return server
end

export ServerState, init_server_state, get_state
export start_api_server, parse_prover
