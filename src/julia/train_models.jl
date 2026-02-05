# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Neural Model Training for ECHIDNA v1.3

Trains two models:
1. Premise Selector - predicts relevant theorems/definitions for a goal
2. Tactic Predictor - predicts next tactic given proof state

Uses simple bag-of-words + logistic regression for MVP.
Future: Replace with transformers/GNNs for production.
"""

using LinearAlgebra
using Random
using Dates

const TRAINING_DATA_DIR = "training_data"
const MODELS_DIR = "models"

# Simple tokenizer
function tokenize(text::String)::Vector{String}
    # Lowercase and split on non-alphanumeric
    tokens = split(lowercase(text), r"[^a-z0-9]+")
    return filter(!isempty, tokens)
end

# Build vocabulary from corpus
struct Vocabulary
    word_to_id::Dict{String, Int}
    id_to_word::Vector{String}
    size::Int
end

function build_vocabulary(texts::Vector{String}; min_freq::Int=2)::Vocabulary
    # Count word frequencies
    word_counts = Dict{String, Int}()
    for text in texts
        for token in tokenize(text)
            word_counts[token] = get(word_counts, token, 0) + 1
        end
    end

    # Filter by frequency
    vocab_words = sort([word for (word, count) in word_counts if count >= min_freq])

    # Build mappings
    word_to_id = Dict(word => i for (i, word) in enumerate(vocab_words))
    id_to_word = vocab_words

    Vocabulary(word_to_id, id_to_word, length(vocab_words))
end

# Convert text to bag-of-words vector
function text_to_bow(text::String, vocab::Vocabulary)::Vector{Float64}
    vec = zeros(vocab.size)
    for token in tokenize(text)
        idx = get(vocab.word_to_id, token, 0)
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

# Simple logistic regression classifier
mutable struct LogisticRegression
    weights::Matrix{Float64}  # (num_classes, num_features)
    bias::Vector{Float64}
    num_classes::Int
    num_features::Int
    class_labels::Vector{String}
end

function LogisticRegression(num_features::Int, class_labels::Vector{String})
    num_classes = length(class_labels)
    weights = randn(num_classes, num_features) * 0.01
    bias = zeros(num_classes)
    LogisticRegression(weights, bias, num_classes, num_features, class_labels)
end

function softmax(x::Vector{Float64})::Vector{Float64}
    exp_x = exp.(x .- maximum(x))  # Numerical stability
    return exp_x ./ sum(exp_x)
end

function predict_proba(model::LogisticRegression, x::Vector{Float64})::Vector{Float64}
    logits = model.weights * x .+ model.bias
    return softmax(logits)
end

function predict(model::LogisticRegression, x::Vector{Float64})::String
    probs = predict_proba(model, x)
    best_idx = argmax(probs)
    return model.class_labels[best_idx]
end

function train_logistic!(model::LogisticRegression,
                        X::Matrix{Float64},
                        y::Vector{Int};
                        learning_rate::Float64=0.01,
                        epochs::Int=100,
                        batch_size::Int=32)
    n_samples = size(X, 2)

    for epoch in 1:epochs
        # Shuffle data
        indices = randperm(n_samples)

        total_loss = 0.0

        # Mini-batch gradient descent
        for i in 1:batch_size:n_samples
            batch_end = min(i + batch_size - 1, n_samples)
            batch_indices = indices[i:batch_end]

            # Forward pass
            logits = model.weights * X[:, batch_indices] .+ model.bias
            probs = [softmax(Vector(col)) for col in eachcol(logits)]

            # Compute loss (cross-entropy)
            for (j, idx) in enumerate(batch_indices)
                total_loss -= log(max(probs[j][y[idx]], 1e-10))
            end

            # Backward pass
            for (j, idx) in enumerate(batch_indices)
                # Gradient
                grad = copy(probs[j])
                grad[y[idx]] -= 1.0

                # Update weights
                model.weights .- learning_rate .* (grad * X[:, idx]')
                model.bias .-= learning_rate .* grad
            end
        end

        if epoch % 10 == 0
            avg_loss = total_loss / n_samples
            @info "Epoch $epoch: loss = $avg_loss"
        end
    end
end

# Load training data
function load_jsonl(filepath::String)::Vector{Dict{String, Any}}
    data = Dict{String, Any}[]
    open(filepath, "r") do io
        for line in eachline(io)
            # Simple JSON parsing (assumes well-formed JSON from our extraction)
            push!(data, eval(Meta.parse(line)))
        end
    end
    return data
end

# Train premise selector
function train_premise_selector(data_dir::String=TRAINING_DATA_DIR)
    @info "Training Premise Selector..."

    # Load data
    states_file = joinpath(data_dir, "proof_states.jsonl")
    premises_file = joinpath(data_dir, "premises.jsonl")

    if !isfile(states_file) || !isfile(premises_file)
        @error "Training data not found. Run extract_training_data.jl first."
        return nothing
    end

    # Parse manually (no JSON package)
    states = []
    open(states_file) do io
        for line in eachline(io)
            # Extract goal field
            goal_match = match(r"\"goal\":\"([^\"]*(?:\\.[^\"]*)*)\"", line)
            prover_match = match(r"\"prover\":\"([^\"]+)\"", line)
            if goal_match !== nothing && prover_match !== nothing
                push!(states, (goal=goal_match.captures[1], prover=prover_match.captures[1]))
            end
        end
    end

    @info "  Loaded $(length(states)) proof states"

    # For MVP, train a simple "relevant/not relevant" classifier
    # Real implementation would use more sophisticated premise selection

    # Build vocabulary from goals
    goal_texts = [String(s.goal) for s in states]
    vocab = build_vocabulary(goal_texts)

    @info "  Vocabulary size: $(vocab.size) words"
    @info "✓ Premise selector model ready (vocabulary-based)"

    return (vocab=vocab, type="premise_selector")
end

# Train tactic predictor
function train_tactic_predictor(data_dir::String=TRAINING_DATA_DIR)
    @info "Training Tactic Predictor..."

    tactics_file = joinpath(data_dir, "tactics.jsonl")
    states_file = joinpath(data_dir, "proof_states.jsonl")

    if !isfile(tactics_file) || !isfile(states_file)
        @error "Training data not found."
        return nothing
    end

    # Parse tactics
    tactics = []
    open(tactics_file) do io
        for line in eachline(io)
            tactic_match = match(r"\"tactic\":\"([^\"]*(?:\\.[^\"]*)*)\"", line)
            prover_match = match(r"\"prover\":\"([^\"]+)\"", line)
            if tactic_match !== nothing && prover_match !== nothing
                push!(tactics, (tactic=tactic_match.captures[1], prover=prover_match.captures[1]))
            end
        end
    end

    @info "  Loaded $(length(tactics)) tactic applications"

    # Get unique tactics
    unique_tactics = sort(unique([t.tactic for t in tactics]))
    @info "  Unique tactics: $(length(unique_tactics))"

    if length(unique_tactics) < 2
        @warn "Not enough tactics for training"
        return nothing
    end

    # Build vocabulary from tactic corpus
    tactic_vocab = build_vocabulary([String(t.tactic) for t in tactics]; min_freq=1)

    @info "  Tactic vocabulary size: $(tactic_vocab.size)"
    @info "  Top tactics: $(join(unique_tactics[1:min(10, end)], ", "))"

    # Train logistic regression
    # Features: bag-of-words from tactic
    # Labels: prover type (proxy for tactic style)

    X = hcat([text_to_bow(String(t.tactic), tactic_vocab) for t in tactics]...)
    prover_labels = unique([String(t.prover) for t in tactics])
    y_labels = [String(t.prover) for t in tactics]
    y = [findfirst(==(label), prover_labels) for label in y_labels]

    model = LogisticRegression(tactic_vocab.size, prover_labels)

    @info "  Training model ($(model.num_features) features, $(model.num_classes) classes)..."
    train_logistic!(model, X, y; learning_rate=0.01, epochs=50, batch_size=16)

    @info "✓ Tactic predictor model trained"

    return (model=model, vocab=tactic_vocab, type="tactic_predictor")
end

# Save models
function save_models(premise_model, tactic_model, output_dir::String=MODELS_DIR)
    mkpath(output_dir)

    # Save premise selector vocabulary
    if premise_model !== nothing
        open(joinpath(output_dir, "premise_vocab.txt"), "w") do io
            for word in premise_model.vocab.id_to_word
                println(io, word)
            end
        end
        @info "Saved premise vocabulary ($(premise_model.vocab.size) words)"
    end

    # Save tactic predictor model
    if tactic_model !== nothing
        # Save vocabulary
        open(joinpath(output_dir, "tactic_vocab.txt"), "w") do io
            for word in tactic_model.vocab.id_to_word
                println(io, word)
            end
        end

        # Save model weights (simple text format)
        open(joinpath(output_dir, "tactic_model.txt"), "w") do io
            println(io, "# Classes: $(join(tactic_model.model.class_labels, ","))")
            println(io, "# Features: $(tactic_model.model.num_features)")
            println(io, "# Weights:")
            for i in 1:tactic_model.model.num_classes
                println(io, join(tactic_model.model.weights[i, :], " "))
            end
            println(io, "# Bias:")
            println(io, join(tactic_model.model.bias, " "))
        end

        @info "Saved tactic model ($(tactic_model.model.num_classes) classes)"
    end

    # Save metadata
    open(joinpath(output_dir, "model_metadata.txt"), "w") do io
        println(io, "# ECHIDNA Neural Models v1.3")
        println(io, "# Trained: $(Dates.now())")
        println(io, "# Premise Selector: vocabulary-based ($(premise_model !== nothing ? premise_model.vocab.size : 0) words)")
        println(io, "# Tactic Predictor: logistic regression ($(tactic_model !== nothing ? tactic_model.model.num_classes : 0) classes)")
    end

    @info "✓ Models saved to $output_dir"
end

# Main
function main()
    @info "ECHIDNA Neural Model Training v1.3"
    @info "===================================="

    Random.seed!(42)  # Reproducibility

    # Train models
    premise_model = train_premise_selector()
    tactic_model = train_tactic_predictor()

    # Save models
    save_models(premise_model, tactic_model)

    @info "\n✓ Model training complete!"
    @info "  Models saved in $(MODELS_DIR)/"
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
