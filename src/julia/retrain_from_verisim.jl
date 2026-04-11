# SPDX-License-Identifier: EUPL-1.2
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# retrain_from_verisim.jl — Retrain ECHIDNA's logistic-regression premise
# selector from VeriSimDB proof_attempts outcomes.
#
# Usage:
#   julia --project=src/julia src/julia/retrain_from_verisim.jl [OPTIONS]
#
# Options (all optional):
#   --verisim-url URL      Base URL of verisim-api (default: $VERISIM_URL or
#                          http://localhost:8080)
#   --ml-url URL           ECHIDNA Julia ML server URL (default: $ECHIDNA_ML_URL
#                          or http://127.0.0.1:8090)
#   --models-dir PATH      Directory for model artefacts (default: models/)
#   --limit N              Max rows to fetch from proof_attempts (default: 20000)
#   --min-samples N        Minimum samples to proceed with training (default: 50)
#   --no-reload            Write files but skip POST /reload to ML server
#
# What this script does:
#
#   1. Fetch proof_attempts rows from VeriSimDB
#      (`GET /api/v1/proof_attempts?limit=N`).
#      If row-level access is unavailable, fall back to the aggregate
#      strategy endpoint and synthesise weighted rows.
#
#   2. Filter to successful and failed attempts (discard "unknown").
#      Retain only rows with non-empty claim text for vocabulary building.
#
#   3. Compute per-prover class weights that upsample minority provers.
#      The training corpus is dominated by Metamath (≈99.6% of attempts).
#      Inverse-frequency weighting gives Lean, Isabelle, Coq, Agda, etc.
#      equal influence during gradient descent.
#
#   4. Grow the premise vocabulary from claim texts of *successful* attempts.
#      New tokens are appended to the existing vocab (tactic_vocab.txt) up
#      to a cap of 2000 words; existing entries are preserved unchanged so
#      the model's feature space only expands, never shrinks.
#
#   5. Retrain the logistic-regression premise selector (L-BFGS-style via
#      gradient descent with momentum) on the weighted dataset.
#
#   6. Write updated model artefacts in the same format that api_server.jl
#      expects (tactic_model.txt + tactic_vocab.txt + premise_vocab.txt).
#
#   7. POST /reload to the ECHIDNA Julia ML server (port 8090) to hot-swap
#      the live models. The server reloads from disk without restarting.
#
# Prover-agnosticism: the script discovers all prover classes present in
# the proof_attempts table at runtime. No hardcoded prover list. Adding a
# new prover to ECHIDNA automatically includes it in the next training run.

using Pkg
Pkg.activate(joinpath(@__DIR__))

using Dates
using HTTP
using JSON3
using LinearAlgebra
using Logging
using Random

# ── Argument parsing ──────────────────────────────────────────────────────────

function parse_args(args)
    opts = Dict{Symbol,Any}(
        :verisim_url   => get(ENV, "VERISIM_URL", "http://localhost:8080"),
        :ml_url        => get(ENV, "ECHIDNA_ML_URL", "http://127.0.0.1:8090"),
        :models_dir    => joinpath(@__DIR__, "..", "..", "models"),
        :limit         => 20_000,
        :min_samples   => 50,
        :do_reload     => true,
    )
    i = 1
    while i <= length(args)
        a = args[i]
        if a == "--verisim-url" && i < length(args)
            opts[:verisim_url] = args[i + 1]; i += 2
        elseif a == "--ml-url" && i < length(args)
            opts[:ml_url] = args[i + 1]; i += 2
        elseif a == "--models-dir" && i < length(args)
            opts[:models_dir] = args[i + 1]; i += 2
        elseif a == "--limit" && i < length(args)
            opts[:limit] = parse(Int, args[i + 1]); i += 2
        elseif a == "--min-samples" && i < length(args)
            opts[:min_samples] = parse(Int, args[i + 1]); i += 2
        elseif a == "--no-reload"
            opts[:do_reload] = false; i += 1
        else
            @warn "Unknown argument: $a"
            i += 1
        end
    end
    opts
end

# ── VeriSimDB fetching ────────────────────────────────────────────────────────

"""
    fetch_proof_attempts(base_url, limit) -> Vector{Dict}

Fetch proof_attempts rows from VeriSimDB's REST API.
Falls back to synthesising rows from the strategy aggregate endpoint when
the row-level `GET /api/v1/proof_attempts` is unavailable.

Each returned dict has at least: "claim", "prover_used", "outcome",
"obligation_class", "duration_ms", "confidence".
"""
function fetch_proof_attempts(base_url::String, limit::Int)::Vector{Dict}
    url = "$(rstrip(base_url, '/'))/api/v1/proof_attempts?limit=$(limit)"
    @info "Fetching proof_attempts" url

    try
        resp = HTTP.get(url; readtimeout=30, connect_timeout=10)
        if resp.status == 200
            rows = JSON3.read(String(resp.body), Vector{Dict})
            @info "  Fetched $(length(rows)) rows from proof_attempts"
            return rows
        end
    catch e
        @warn "Row-level endpoint unavailable, falling back to strategy aggregates" error=e
    end

    # ── Fallback: synthesise from strategy endpoint ──────────────────────────
    @info "  Synthesising rows from /api/v1/proof_attempts/strategy"
    synthesise_from_strategy(base_url, limit)
end

"""
Synthesise weighted attempt rows from the strategy aggregate endpoint.
Each aggregate record → N synthetic rows (proportional to total_attempts).
"""
function synthesise_from_strategy(base_url::String, limit::Int)::Vector{Dict}
    classes = [
        "safety", "linearity", "termination", "equiv", "correctness",
        "confluence", "totality", "invariant", "refinement", "model-check",
        "metamath_proof", "coq_proof", "lean_proof", "agda_proof",
        "isabelle_proof", "z3_proof", "cvc5_proof", "mizar_proof", "other"
    ]

    rows = Dict[]

    for class in classes
        url = "$(rstrip(base_url, '/'))/api/v1/proof_attempts/strategy?class=$(class)&limit=20"
        try
            resp = HTTP.get(url; readtimeout=10, connect_timeout=5)
            resp.status == 200 || continue
            data = JSON3.read(String(resp.body))
            recs = get(data, "recommendations", get(data, "data", []))

            for rec in recs
                prover = get(rec, "prover", get(rec, "prover_used", "other"))
                rate   = get(rec, "success_rate", 0.5)
                n_total = min(get(rec, "total_attempts", 1), div(limit, max(length(recs), 1)))

                n_success = round(Int, n_total * rate)
                n_fail    = n_total - n_success

                for _ in 1:n_success
                    push!(rows, Dict(
                        "claim"            => "$(class) proof obligation",
                        "prover_used"      => string(prover),
                        "outcome"          => "success",
                        "obligation_class" => class,
                        "duration_ms"      => get(rec, "avg_duration_ms", 1000),
                        "confidence"       => rate
                    ))
                end
                for _ in 1:n_fail
                    push!(rows, Dict(
                        "claim"            => "$(class) proof obligation",
                        "prover_used"      => string(prover),
                        "outcome"          => "failure",
                        "obligation_class" => class,
                        "duration_ms"      => get(rec, "avg_duration_ms", 1000),
                        "confidence"       => rate
                    ))
                end
            end
        catch _
            continue
        end
    end

    @info "  Synthesised $(length(rows)) rows from strategy aggregates"
    rows
end

# ── Data preparation ──────────────────────────────────────────────────────────

"""
    prepare_training_data(rows) -> (X, y_idx, classes, class_weights)

Build a bag-of-words feature matrix from claim texts, a class-index label
vector, the ordered class list, and inverse-frequency class weights.

Filters out "unknown" outcomes. Provers with < 3 samples are kept but
receive very high weight so they are not drowned by Metamath.
"""
function prepare_training_data(rows::Vector, vocab::Vector{String})
    # Discard rows with unknown outcome
    valid = filter(r -> get(r, "outcome", "unknown") in ("success", "failure"), rows)

    if isempty(valid)
        error("No valid rows after filtering (need outcome = success or failure)")
    end

    # Discover all provers present — prover-agnostic
    provers = sort(unique(string(get(r, "prover_used", "other")) for r in valid))
    prover_index = Dict(p => i for (i, p) in enumerate(provers))
    n_classes = length(provers)
    n_features = length(vocab)

    @info "  Classes ($(n_classes)): $(join(provers, ", "))"
    @info "  Features: $(n_features)"

    word_idx = Dict(w => i for (i, w) in enumerate(vocab))

    X = zeros(Float64, length(valid), n_features)
    y = zeros(Int, length(valid))

    for (i, row) in enumerate(valid)
        claim  = string(get(row, "claim", ""))
        prover = string(get(row, "prover_used", "other"))
        tokens = tokenize(claim)
        for tok in tokens
            j = get(word_idx, tok, 0)
            if j > 0
                X[i, j] += 1.0
            end
        end
        # L1-normalise each row
        s = sum(X[i, :])
        if s > 0
            X[i, :] ./= s
        end
        y[i] = get(prover_index, prover, n_classes)  # fallback to last class
    end

    # Inverse-frequency class weights to address Metamath dominance
    counts = [count(==(j), y) for j in 1:n_classes]
    total  = length(y)
    weights = [total / (n_classes * max(c, 1)) for c in counts]
    # Cap max weight at 100× median to avoid extreme upsampling of singletons
    med_w = sort(weights)[div(length(weights), 2) + 1]
    weights = clamp.(weights, 0.0, med_w * 100.0)
    weights ./= sum(weights)  # normalise

    @info "  Class weights ($(n_classes) provers):"
    for (p, w, c) in zip(provers, weights, counts)
        @info "    $(lpad(p, 12)): weight=$(round(w, digits=4))  samples=$(c)"
    end

    X, y, provers, weights
end

# ── Tokeniser ─────────────────────────────────────────────────────────────────

function tokenize(text::String)::Vector{String}
    tokens = split(lowercase(text), r"[^a-z0-9_]+")
    filter(!isempty, tokens)
end

# ── Vocabulary growth ─────────────────────────────────────────────────────────

"""
    grow_vocab(existing_vocab, successful_rows; max_vocab) -> Vector{String}

Append new tokens from successful proof attempt claims to the vocabulary.
Existing entries are preserved unchanged. Returns the extended vocab.
"""
function grow_vocab(
    existing::Vector{String},
    rows::Vector,
    max_vocab::Int = 2000
)::Vector{String}
    existing_set = Set(existing)
    token_freq   = Dict{String,Int}()

    for row in rows
        get(row, "outcome", "failure") == "success" || continue
        claim = string(get(row, "claim", ""))
        for tok in tokenize(claim)
            length(tok) >= 3 || continue  # skip very short tokens
            token_freq[tok] = get(token_freq, tok, 0) + 1
        end
    end

    # Remove tokens already in vocab
    new_tokens = [(tok, freq) for (tok, freq) in token_freq if tok ∉ existing_set]
    # Sort by frequency descending, take top N to fill up to max_vocab
    sort!(new_tokens; by = x -> -x[2])
    slots = max(0, max_vocab - length(existing))
    appended = [tok for (tok, _) in new_tokens[1:min(end, slots)]]

    extended = vcat(existing, appended)
    @info "  Vocab: $(length(existing)) existing + $(length(appended)) new = $(length(extended))"
    extended
end

# ── Logistic regression (softmax, SGD with momentum) ─────────────────────────

"""
    train_logistic(X, y, n_classes, class_weights; epochs, lr, momentum)
      -> (W, b)

Softmax logistic regression trained with stochastic gradient descent and
momentum. Class weights are applied per-sample to balance the loss.

Returns weight matrix W (n_classes × n_features) and bias vector b
(n_classes,) in the same format as the existing tactic_model.txt.
"""
function train_logistic(
    X::Matrix{Float64},
    y::Vector{Int},
    n_classes::Int,
    class_weights::Vector{Float64};
    epochs::Int = 50,
    lr::Float64 = 0.05,
    momentum::Float64 = 0.9,
    batch_size::Int = 128
)
    n_samples, n_features = size(X)
    W = randn(n_classes, n_features) .* 0.01
    b = zeros(n_classes)
    dW = zeros(size(W))
    db = zeros(size(b))

    for epoch in 1:epochs
        # Shuffle
        idx = randperm(n_samples)
        total_loss = 0.0

        for start in 1:batch_size:n_samples
            batch = idx[start:min(start + batch_size - 1, n_samples)]
            Xb = X[batch, :]
            yb = y[batch]

            # Forward pass: softmax
            logits = Xb * W' .+ b'           # (B × n_classes)
            logits .-= maximum(logits; dims=2) # numerical stability
            exp_l  = exp.(logits)
            probs  = exp_l ./ sum(exp_l; dims=2)   # (B × n_classes)

            # Sample weights (inverse-frequency)
            sw = [class_weights[yi] for yi in yb]

            # Loss (weighted cross-entropy)
            for (i, yi) in enumerate(yb)
                total_loss -= sw[i] * log(max(probs[i, yi], 1e-12))
            end

            # Backward pass
            delta = copy(probs)
            for (i, yi) in enumerate(yb)
                delta[i, yi] -= 1.0
                delta[i, :] .*= sw[i]
            end

            gW = delta' * Xb ./ length(batch)   # (n_classes × n_features)
            gb = vec(sum(delta; dims=1)) ./ length(batch)

            # Momentum update
            dW .= momentum .* dW .+ lr .* gW
            db .= momentum .* db .+ lr .* gb
            W .-= dW
            b .-= db
        end

        if epoch % 10 == 0 || epoch == epochs
            avg_loss = total_loss / n_samples
            @info "  Epoch $(lpad(epoch, 3))/$(epochs): loss=$(round(avg_loss, digits=4))"
        end
    end

    W, b
end

# ── Model file I/O ────────────────────────────────────────────────────────────

function load_vocab(path::String)::Vector{String}
    isfile(path) || return String[]
    filter(!isempty, strip.(readlines(path)))
end

function save_vocab(vocab::Vector{String}, path::String)
    open(path, "w") do io
        for word in vocab
            println(io, word)
        end
    end
end

function save_tactic_model(W, b, classes::Vector{String}, n_features::Int, path::String)
    open(path, "w") do io
        println(io, "# Classes: $(join(classes, ","))")
        println(io, "# Features: $(n_features)")
        println(io, "# Weights:")
        for row in eachrow(W)
            println(io, join(row, " "))
        end
        println(io, "# Bias:")
        println(io, join(b, " "))
    end
end

# ── Hot-reload via ML server ──────────────────────────────────────────────────

"""
    reload_ml_server(ml_url) -> Bool

POST /reload to the ECHIDNA Julia ML server to hot-swap the live model
from disk without restarting the process. Returns true on success.
"""
function reload_ml_server(ml_url::String)::Bool
    url = "$(rstrip(ml_url, '/'))/reload"
    @info "Triggering hot-reload" url
    try
        resp = HTTP.post(url; readtimeout=30, connect_timeout=10)
        if resp.status == 200
            data = JSON3.read(String(resp.body))
            @info "  Reload acknowledged" status=get(data, "status", "ok")
            return true
        else
            @warn "  Reload returned HTTP $(resp.status)"
            return false
        end
    catch e
        @warn "  Reload failed — ML server may not be running" error=e
        return false
    end
end

# ── Main ──────────────────────────────────────────────────────────────────────

function main(args=ARGS)
    opts = parse_args(args)

    println("╔═══════════════════════════════════════════════════════╗")
    println("║  ECHIDNA — VeriSimDB-driven premise-selector retrain  ║")
    println("╚═══════════════════════════════════════════════════════╝")
    println()
    @info "Config" verisim_url=opts[:verisim_url]
    @info "Config" ml_url=opts[:ml_url] models_dir=opts[:models_dir] limit=opts[:limit]
    println()

    models_dir = opts[:models_dir]
    vocab_path  = joinpath(models_dir, "tactic_vocab.txt")
    model_path  = joinpath(models_dir, "tactic_model.txt")
    premise_path = joinpath(models_dir, "premise_vocab.txt")

    # ── Step 1: Fetch proof_attempts ──────────────────────────────────────────
    println("═══════════════════════════════════════════════════════")
    println("Step 1/6 — Fetching proof_attempts from VeriSimDB")
    println("═══════════════════════════════════════════════════════")
    rows = fetch_proof_attempts(opts[:verisim_url], opts[:limit])
    println()

    if length(rows) < opts[:min_samples]
        @warn "Too few samples ($(length(rows)) < $(opts[:min_samples])). Aborting retrain."
        @warn "Possible causes: VeriSimDB not yet populated, or echidnabot HYPATIA_VERISIM_URL unset."
        return 1
    end

    # ── Step 2: Load existing vocabulary ─────────────────────────────────────
    println("═══════════════════════════════════════════════════════")
    println("Step 2/6 — Loading existing vocabulary")
    println("═══════════════════════════════════════════════════════")
    existing_vocab = load_vocab(vocab_path)
    @info "  Existing vocab: $(length(existing_vocab)) words"
    println()

    # ── Step 3: Grow vocab from successful claims ─────────────────────────────
    println("═══════════════════════════════════════════════════════")
    println("Step 3/6 — Growing vocabulary from successful traces")
    println("═══════════════════════════════════════════════════════")
    vocab = grow_vocab(existing_vocab, rows, 2000)
    println()

    # ── Step 4: Prepare weighted training data ────────────────────────────────
    println("═══════════════════════════════════════════════════════")
    println("Step 4/6 — Preparing weighted training data")
    println("═══════════════════════════════════════════════════════")
    X, y, classes, class_weights = prepare_training_data(rows, vocab)
    @info "  Training samples: $(length(y))"
    println()

    # ── Step 5: Retrain logistic regression ───────────────────────────────────
    println("═══════════════════════════════════════════════════════")
    println("Step 5/6 — Retraining logistic regression")
    println("═══════════════════════════════════════════════════════")
    @info "  Starting SGD (epochs=50, lr=0.05, momentum=0.9, batch=128)"
    W, b = train_logistic(X, y, length(classes), class_weights;
                           epochs=50, lr=0.05, momentum=0.9, batch_size=128)
    println()

    # Quick accuracy report
    logits = X * W' .+ b'
    preds  = [argmax(logits[i, :]) for i in axes(logits, 1)]
    acc    = count(preds .== y) / length(y)
    @info "  Training accuracy: $(round(100acc, digits=1))%"
    println()

    # ── Step 6: Write model artefacts ─────────────────────────────────────────
    println("═══════════════════════════════════════════════════════")
    println("Step 6/6 — Writing model artefacts")
    println("═══════════════════════════════════════════════════════")
    mkpath(models_dir)

    save_vocab(vocab, vocab_path)
    @info "  Saved vocab: $vocab_path ($(length(vocab)) words)"

    save_tactic_model(W, b, classes, length(vocab), model_path)
    @info "  Saved model: $model_path ($(length(classes)) classes × $(length(vocab)) features)"

    # Also write premise_vocab.txt with the full extended vocab
    # (it was empty before — now populated from successful traces)
    save_vocab(vocab, premise_path)
    @info "  Saved premise vocab: $premise_path"

    # Write a metadata file recording what this run did
    meta_path = joinpath(models_dir, "retrain_metadata.txt")
    open(meta_path, "w") do io
        println(io, "retrained_at: $(Dates.now(UTC))")
        println(io, "source: VeriSimDB proof_attempts")
        println(io, "rows_fetched: $(length(rows))")
        println(io, "vocab_size: $(length(vocab))")
        println(io, "classes: $(join(classes, ","))")
        println(io, "training_accuracy: $(round(100acc, digits=1))%")
    end
    println()

    # ── Optional: Hot-reload ML server ────────────────────────────────────────
    if opts[:do_reload]
        reload_ml_server(opts[:ml_url])
    else
        @info "Skipping reload (--no-reload)"
    end

    println()
    println("✓ Retraining complete.")
    println("  Provers: $(join(classes, ", "))")
    println("  Vocab size: $(length(vocab))")
    println("  Training accuracy: $(round(100acc, digits=1))%")
    return 0
end

exit(main(ARGS))
