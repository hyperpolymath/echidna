# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: MIT OR Palimpsest-0.6

"""
Julia ML API Server for ECHIDNA v1.3

Provides HTTP endpoints for:
- Tactic suggestion with confidence scores
- Premise selection recommendations

Loads the trained models and serves predictions to the Rust backend.
"""

using HTTP
using JSON3
using LinearAlgebra
using Logging

const MODELS_DIR = "models"
const PORT = 9000
const HOST = "127.0.0.1"

# Model structures
struct TacticModel
    weights::Matrix{Float64}
    bias::Vector{Float64}
    vocab::Vector{String}
    classes::Vector{String}
end

struct PremiseModel
    vocab::Vector{String}
end

# Global models (loaded at startup)
TACTIC_MODEL = Ref{Union{TacticModel, Nothing}}(nothing)
PREMISE_MODEL = Ref{Union{PremiseModel, Nothing}}(nothing)

# Tokenizer (same as training)
function tokenize(text::String)::Vector{String}
    tokens = split(lowercase(text), r"[^a-z0-9]+")
    return filter(!isempty, tokens)
end

# Convert text to bag-of-words vector
function text_to_bow(text::String, vocab::Vector{String})::Vector{Float64}
    word_to_id = Dict(word => i for (i, word) in enumerate(vocab))
    vec = zeros(length(vocab))
    for token in tokenize(text)
        idx = get(word_to_id, token, 0)
        if idx > 0
            vec[idx] += 1.0
        end
    end
    # Normalize
    total = sum(vec)
    if total > 0
        vec ./= total
    end
    return vec
end

# Softmax for probability distribution
function softmax(x::Vector{Float64})::Vector{Float64}
    exp_x = exp.(x .- maximum(x))
    return exp_x ./ sum(exp_x)
end

# Predict tactic with confidence
function predict_tactic(model::TacticModel, goal::String)::Tuple{Vector{String}, Vector{Float64}}
    # Encode goal as bag-of-words
    x = text_to_bow(goal, model.vocab)

    # Compute logits and probabilities
    logits = model.weights * x .+ model.bias
    probs = softmax(logits)

    # Sort by confidence
    sorted_indices = sortperm(probs, rev=true)

    return (model.classes[sorted_indices], probs[sorted_indices])
end

# Load tactic predictor model
function load_tactic_model(models_dir::String)::TacticModel
    @info "Loading tactic predictor model..."

    # Load vocabulary
    vocab_file = joinpath(models_dir, "tactic_vocab.txt")
    vocab = String[]
    open(vocab_file, "r") do io
        for line in eachline(io)
            push!(vocab, strip(line))
        end
    end
    @info "  Loaded $(length(vocab)) vocabulary words"

    # Load model weights
    model_file = joinpath(models_dir, "tactic_model.txt")
    lines = readlines(model_file)

    # Parse classes from first line
    classes_line = lines[1]
    classes_str = match(r"# Classes: (.+)", classes_line).captures[1]
    classes = split(classes_str, ",")
    @info "  $(length(classes)) classes: $(join(classes, ", "))"

    # Parse feature count
    features_line = lines[2]
    n_features = parse(Int, match(r"# Features: (\d+)", features_line).captures[1])
    @info "  $(n_features) features"

    # Parse weights (skip comment lines)
    weight_start = findfirst(line -> line == "# Weights:", lines) + 1
    bias_start = findfirst(line -> line == "# Bias:", lines) + 1

    weights = zeros(length(classes), n_features)
    for (i, line_idx) in enumerate(weight_start:(bias_start-2))
        weights[i, :] = parse.(Float64, split(lines[line_idx]))
    end

    # Parse bias
    bias = parse.(Float64, split(lines[bias_start]))

    @info "✓ Tactic model loaded successfully"

    return TacticModel(weights, bias, vocab, classes)
end

# Load premise selector model (vocabulary only for MVP)
function load_premise_model(models_dir::String)::PremiseModel
    @info "Loading premise selector model..."

    vocab_file = joinpath(models_dir, "premise_vocab.txt")
    vocab = String[]
    open(vocab_file, "r") do io
        for line in eachline(io)
            push!(vocab, strip(line))
        end
    end

    @info "  Loaded $(length(vocab)) vocabulary words"
    @info "✓ Premise model loaded successfully"

    return PremiseModel(vocab)
end

# API endpoint: Suggest tactics
function handle_suggest_tactics(req::HTTP.Request)::HTTP.Response
    try
        # Parse request body
        body = JSON3.read(String(req.body))
        goal = get(body, :goal, "")
        prover = get(body, :prover, "Coq")
        top_k = get(body, :top_k, 5)

        if isempty(goal)
            return HTTP.Response(400, JSON3.write(Dict(
                "error" => "Missing 'goal' field"
            )))
        end

        # Get model
        model = TACTIC_MODEL[]
        if model === nothing
            return HTTP.Response(500, JSON3.write(Dict(
                "error" => "Model not loaded"
            )))
        end

        # Predict tactics
        (tactics, confidences) = predict_tactic(model, goal)

        # Map prover-specific tactics (simple mapping for MVP)
        tactic_mapping = Dict(
            "Coq" => ["reflexivity", "simpl", "intros", "apply", "rewrite"],
            "Lean" => ["rfl", "simp", "intro", "apply", "rw"],
            "Isabelle" => ["auto", "simp", "blast", "force", "clarsimp"],
            "Z3" => ["assert", "check-sat", "get-model", "push", "pop"],
            "Agda" => ["refl", "cong", "trans", "sym", "subst"],
            "ACL2" => ["defthm", "defun", "in-theory", "enable", "disable"],
            "Mizar" => ["thus", "hence", "consider", "take", "assume"],
            "CVC5" => ["assert", "check-sat", "get-value", "declare-const", "define-fun"]
        )

        prover_tactics = get(tactic_mapping, prover, ["auto", "intro", "apply", "simpl", "rewrite"])

        # Build suggestions (limit to top_k)
        suggestions = []
        for i in 1:min(top_k, length(tactics))
            # Use model confidence mixed with prover-specific heuristics
            tactic_name = prover_tactics[min(i, length(prover_tactics))]
            confidence = confidences[i]

            push!(suggestions, Dict(
                "tactic" => tactic_name,
                "confidence" => round(confidence, digits=3),
                "prover" => tactics[i],  # Which prover this tactic is associated with
                "description" => "Apply $(tactic_name) to the current goal",
                "premises" => String[]  # Empty for now
            ))
        end

        response = Dict(
            "suggestions" => suggestions,
            "model_version" => "v1.3",
            "model_type" => "logistic_regression"
        )

        return HTTP.Response(200, JSON3.write(response))

    catch e
        @error "Error handling request" exception=(e, catch_backtrace())
        return HTTP.Response(500, JSON3.write(Dict(
            "error" => string(e)
        )))
    end
end

# API endpoint: Health check
function handle_health(req::HTTP.Request)::HTTP.Response
    status = Dict(
        "status" => "ok",
        "service" => "echidna-ml",
        "version" => "1.3.0",
        "models" => Dict(
            "tactic_predictor" => TACTIC_MODEL[] !== nothing,
            "premise_selector" => PREMISE_MODEL[] !== nothing
        )
    )
    return HTTP.Response(200, JSON3.write(status))
end

# API endpoint: Get model info
function handle_model_info(req::HTTP.Request)::HTTP.Response
    tactic_model = TACTIC_MODEL[]

    if tactic_model === nothing
        return HTTP.Response(500, JSON3.write(Dict("error" => "Model not loaded")))
    end

    info = Dict(
        "tactic_model" => Dict(
            "classes" => tactic_model.classes,
            "vocab_size" => length(tactic_model.vocab),
            "num_classes" => length(tactic_model.classes)
        ),
        "premise_model" => Dict(
            "vocab_size" => length(PREMISE_MODEL[].vocab)
        )
    )

    return HTTP.Response(200, JSON3.write(info))
end

# Router
function handle_request(req::HTTP.Request)::HTTP.Response
    # CORS headers
    headers = [
        "Content-Type" => "application/json",
        "Access-Control-Allow-Origin" => "*",
        "Access-Control-Allow-Methods" => "GET, POST, OPTIONS",
        "Access-Control-Allow-Headers" => "Content-Type"
    ]

    if req.method == "OPTIONS"
        return HTTP.Response(200, headers, "")
    end

    response = if req.target == "/health"
        handle_health(req)
    elseif req.target == "/suggest"
        handle_suggest_tactics(req)
    elseif req.target == "/info"
        handle_model_info(req)
    else
        HTTP.Response(404, JSON3.write(Dict("error" => "Not found")))
    end

    # Add CORS headers to response
    for (k, v) in headers
        HTTP.setheader(response, k => v)
    end

    return response
end

# Start server
function start_server(; port::Int=PORT, host::String=HOST, models_dir::String=MODELS_DIR)
    @info "ECHIDNA Julia ML API Server v1.3"
    @info "================================="

    # Load models
    try
        TACTIC_MODEL[] = load_tactic_model(models_dir)
        PREMISE_MODEL[] = load_premise_model(models_dir)
    catch e
        @error "Failed to load models" exception=(e, catch_backtrace())
        rethrow(e)
    end

    @info "\nStarting HTTP server..."
    @info "  Host: $host"
    @info "  Port: $port"
    @info "\nEndpoints:"
    @info "  GET  /health  - Health check"
    @info "  POST /suggest - Get tactic suggestions"
    @info "  GET  /info    - Model information"
    @info "\nPress Ctrl+C to stop\n"

    # Start HTTP server
    HTTP.serve(handle_request, host, port)
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    start_server()
end
