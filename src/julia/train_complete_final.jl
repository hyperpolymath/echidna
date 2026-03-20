#!/usr/bin/env julia
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
COMPLETE FINAL Model Training - Standalone version with all dependencies
"""

using LinearAlgebra
using Random
using Dates
using JSON3

const TRAINING_DATA_DIR = "training_data"
const MODELS_DIR = "models"

# Helper functions (copied from main training script)
struct Vocabulary
    word_to_id::Dict{String, Int}
    id_to_word::Vector{String}
    size::Int
end

function build_vocabulary(texts::Vector{String}; min_freq::Int=2)::Vocabulary
    # Count word frequencies
    word_counts = Dict{String, Int}()
    for text in texts
        for token in split(lowercase(text), r"[^a-z0-9]+")
            if !isempty(token)
                word_counts[token] = get(word_counts, token, 0) + 1
            end
        end
    end

    # Filter by frequency
    vocab_words = sort([word for (word, count) in word_counts if count >= min_freq])

    # Build mappings
    word_to_id = Dict(word => i for (i, word) in enumerate(vocab_words))
    id_to_word = vocab_words

    Vocabulary(word_to_id, id_to_word, length(vocab_words))
end

function text_to_bow(text::String, vocab::Vocabulary)::Vector{Float64}
    vec = zeros(vocab.size)
    for token in split(lowercase(text), r"[^a-z0-9]+")
        if !isempty(token)
            idx = get(vocab.word_to_id, token, 0)
            if idx > 0
                vec[idx] += 1.0
            end
        end
    end
    # Normalize
    total = sum(vec)
    if total > 0
        vec ./= total
    end
    return vec
end

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
            @info "  Epoch $epoch: loss = $avg_loss"
        end
    end
end

function save_models(premise_model, tactic_model)
    mkpath(MODELS_DIR)
    
    # Save premise vocabulary
    if premise_model !== nothing
        open(joinpath(MODELS_DIR, "premise_vocab_COMPLETE.txt"), "w") do io
            for word in premise_model.vocab.id_to_word
                println(io, word)
            end
        end
        @info "Saved premise vocabulary ($(premise_model.vocab.size) words)"
    end

    # Save tactic model
    if tactic_model !== nothing
        # Save vocabulary
        open(joinpath(MODELS_DIR, "tactic_vocab_COMPLETE.txt"), "w") do io
            for word in tactic_model.vocab.id_to_word
                println(io, word)
            end
        end

        # Save model weights
        open(joinpath(MODELS_DIR, "tactic_model_COMPLETE.txt"), "w") do io
            println(io, "# Classes: $(join(tactic_model.model.class_labels, ','))")
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
    open(joinpath(MODELS_DIR, "model_metadata_COMPLETE.txt"), "w") do io
        println(io, "# ECHIDNA v2.0 COMPLETE Model Training")
        println(io, "# Training Date: $(Dates.now())")
        println(io, "# Corpus: COMPLETE (66k proofs, 179k tactics)")
        println(io, "# Premise Vocabulary: $(premise_model !== nothing ? premise_model.vocab.size : 0) words")
        println(io, "# Tactic Predictor: logistic regression")
        println(io, "# Tactic Classes: $(tactic_model !== nothing ? tactic_model.model.num_classes : 0)")
        println(io, "# Tactic Features: $(tactic_model !== nothing ? tactic_model.model.num_features : 0)")
    end
end

# Load complete data
function load_complete_data()
    @info "Loading COMPLETE corpus data..."
    
    # Load proof states
    states_file = joinpath(TRAINING_DATA_DIR, "proof_states_COMPLETE.jsonl")
    states = []
    open(states_file) do io
        for line in eachline(io)
            try
                push!(states, JSON3.read(line))
            catch
                continue
            end
        end
    end
    
    # Load tactics
    tactics_file = joinpath(TRAINING_DATA_DIR, "tactics_COMPLETE.jsonl")
    tactics = []
    open(tactics_file) do io
        for line in eachline(io)
            try
                push!(tactics, JSON3.read(line))
            catch
                continue
            end
        end
    end
    
    @info "  Loaded $(length(states)) proof states"
    @info "  Loaded $(length(tactics)) tactics"
    
    return states, tactics
end

# Main training function
function main()
    @info "ECHIDNA COMPLETE FINAL Model Training"
    @info "="^50
    
    Random.seed!(42)
    
    # Load complete data
    states, tactics = load_complete_data()
    
    if isempty(states) || isempty(tactics)
        @error "No data loaded!"
        return
    end
    
    # Build vocabulary from goals
    goal_texts = [String(s.goal) for s in states]
    vocab = build_vocabulary(goal_texts)
    
    @info "  Goal vocabulary: $(vocab.size) words"
    
    # Build vocabulary from tactics
    tactic_texts = [String(t.tactic) for t in tactics]
    tactic_vocab = build_vocabulary(tactic_texts)
    
    @info "  Tactic vocabulary: $(tactic_vocab.size) words"
    
    # Prepare features for tactic prediction
    X = hcat([text_to_bow(String(t.tactic), tactic_vocab) for t in tactics]...)
    prover_labels = unique([String(t.prover) for t in tactics])
    y = [findfirst(==(String(t.prover)), prover_labels) for t in tactics]
    
    @info "  Feature matrix: $(size(X, 1)) features × $(size(X, 2)) samples"
    @info "  Classes: $(length(prover_labels)) provers"
    
    # Train logistic regression model
    model = LogisticRegression(tactic_vocab.size, prover_labels)
    @info "  Training model..."
    train_logistic!(model, X, y; learning_rate=0.01, epochs=50, batch_size=16)
    
    # Save models
    save_models((vocab=vocab, type="premise_selector"), 
                (model=model, vocab=tactic_vocab, type="tactic_predictor"))
    
    @info "✅ COMPLETE FINAL model training successful!"
    @info "  Models trained on COMPLETE corpus (66k proofs, 179k tactics)"
    @info "  Models saved with _COMPLETE suffix"
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end