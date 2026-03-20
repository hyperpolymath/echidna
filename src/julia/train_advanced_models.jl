#!/usr/bin/env julia
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Advanced Neural Model Training for ECHIDNA v2.0

Implements neural networks instead of logistic regression for better performance.
"""

using LinearAlgebra
using Random
using Dates
using Flux
using Flux: @epochs, throttle
using BSON: @save, @load

const TRAINING_DATA_DIR = "training_data"
const MODELS_DIR = "models"
const USE_MAX_DATA = true

# Neural network architecture
struct TacticClassifier
    embedding::Dense
    lstm::LSTM
    classifier::Chain
end

function TacticClassifier(input_size::Int, hidden_size::Int, output_size::Int)
    embedding = Dense(input_size, hidden_size, relu)
    lstm = LSTM(hidden_size, hidden_size)
    classifier = Chain(
        Dense(hidden_size, hidden_size, relu),
        Dropout(0.3),
        Dense(hidden_size, output_size)
    )
    TacticClassifier(embedding, lstm, classifier)
end

function (model::TacticClassifier)(x::Vector{Float32})
    # Reshape for LSTM (seq_len, batch_size, input_size)
    x_reshaped = reshape(x, :, 1, 1)
    embedded = model.embedding(x_reshaped)
    lstm_out, _ = model.lstm(embedded)
    return model.classifier(lstm_out[:, end, :])
end

function loss_function(model, x, y)
    y_pred = model(x)
    return Flux.logitcrossentropy(y_pred, y)
end

function train_neural_model(X::Matrix{Float32}, y::Matrix{Int}, 
                           input_size::Int, output_size::Int; 
                           epochs::Int=100, batch_size::Int=32, lr::Float32=0.001f0)
    
    @info "Training neural network model..."
    @info "  Input size: $input_size, Output size: $output_size"
    @info "  Epochs: $epochs, Batch size: $batch_size, LR: $lr"
    
    # Create model
    hidden_size = 128
    model = TacticClassifier(input_size, hidden_size, output_size)
    
    # Optimizer
    optimizer = ADAM(lr)
    
    # Training data
    n_samples = size(X, 2)
    indices = collect(1:n_samples)
    
    # Training loop
    function report(epoch)
        if epoch % 10 == 0
            @info "  Epoch $epoch/$epochs"
        end
    end
    
    for epoch in 1:epochs
        shuffle!(indices)
        total_loss = 0.0
        correct = 0
        
        for i in 1:batch_size:n_samples
            batch_indices = indices[i:min(i+batch_size-1, n_samples)]
            batch_X = X[:, batch_indices]
            batch_y = y[:, batch_indices]
            
            # Train on batch
            gs = gradient(() -> loss_function(model, batch_X, batch_y), Flux.params(model))
            Flux.Optimise.update!(optimizer, Flux.params(model), gs)
            
            # Calculate batch loss and accuracy
            batch_loss = loss_function(model, batch_X, batch_y)
            total_loss += batch_loss
            
            # Accuracy
            y_pred = model(batch_X)
            predicted = argmax(y_pred, dims=1)
            actual = argmax(batch_y, dims=1)
            correct += sum(predicted .== actual)
        end
        
        avg_loss = total_loss / ceil(n_samples / batch_size)
        accuracy = correct / n_samples
        
        if epoch % 10 == 0
            @info "  Epoch $epoch: loss = $avg_loss, accuracy = $accuracy"
        end
        
        report(epoch)
    end
    
    return model
end

# Enhanced feature extraction
function extract_enhanced_features(text::String, vocab::Vocabulary)::Vector{Float32}
    # Bag of words
    bow = text_to_bow(text, vocab)
    
    # Character n-grams
    char_features = zeros(Float32, 26)  # a-z
    text_lower = lowercase(text)
    for c in text_lower
        if 'a' <= c <= 'z'
            idx = Int(c) - Int('a') + 1
            char_features[idx] += 1
        end
    end
    char_features ./= sum(char_features) + 1e-8
    
    # Length features
    length_features = [
        Float32(length(text)),
        Float32(count(==(' '), text)),  # word count proxy
        Float32(count(c -> isuppercase(c), text))
    ]
    length_features ./= maximum(length_features) + 1e-8
    
    return vcat(Float32.(bow), char_features, length_features)
end

# Load and process MAX data
function load_max_data()
    @info "Loading MAXIMUM corpus data..."
    
    # Load proof states
    states_file = joinpath(TRAINING_DATA_DIR, "proof_states_MAX.jsonl")
    states = []
    open(states_file) do io
        for line in eachline(io)
            goal_match = match(r"\"goal\":\"([^\"]+)\"", line)
            prover_match = match(r"\"prover\":\"([^\"]+)\"", line)
            if goal_match !== nothing && prover_match !== nothing
                push!(states, (goal=goal_match.captures[1], prover=prover_match.captures[1]))
            end
        end
    end
    
    # Load tactics
    tactics_file = joinpath(TRAINING_DATA_DIR, "tactics_MAX.jsonl")
    tactics = []
    open(tactics_file) do io
        for line in eachline(io)
            tactic_match = match(r"\"tactic\":\"([^\"]+)\"", line)
            prover_match = match(r"\"prover\":\"([^\"]+)\"", line)
            if tactic_match !== nothing && prover_match !== nothing
                push!(tactics, (tactic=tactic_match.captures[1], prover=prover_match.captures[1]))
            end
        end
    end
    
    @info "  Loaded $(length(states)) proof states"
    @info "  Loaded $(length(tactics)) tactics"
    
    return states, tactics
end

# Main training function
function main()
    @info "ECHIDNA Advanced Neural Model Training v2.0"
    @info "="^50
    
    Random.seed!(42)
    
    # Load MAX data
    states, tactics = load_max_data()
    
    # Build vocabulary from tactics
    tactic_texts = [t.tactic for t in tactics]
    vocab = build_vocabulary(tactic_texts; min_freq=2)
    
    @info "  Tactic vocabulary: $(vocab.size) words"
    
    # Prepare features and labels
    X = zeros(Float32, vocab.size + 26 + 3, length(tactics))  # bow + chars + length
    prover_labels = unique([t.prover for t in tactics])
    y = zeros(Int, length(prover_labels), length(tactics))
    
    for (i, tactic) in enumerate(tactics)
        features = extract_enhanced_features(tactic.tactic, vocab)
        X[:, i] = features
        
        # One-hot encode prover
        prover_idx = findfirst(==(tactic.prover), prover_labels)
        if prover_idx !== nothing
            y[prover_idx, i] = 1
        end
    end
    
    @info "  Feature matrix: $(size(X, 1)) features × $(size(X, 2)) samples"
    @info "  Classes: $(length(prover_labels)) provers"
    
    # Train neural network
    model = train_neural_model(X, y, size(X, 1), length(prover_labels), 
                              epochs=50, batch_size=64, lr=0.001f0)
    
    # Save model
    mkpath(MODELS_DIR)
    model_file = joinpath(MODELS_DIR, "tactic_nn.bson")
    @save model_file model
    
    # Save metadata
    open(joinpath(MODELS_DIR, "advanced_stats.txt"), "w") do io
        println(io, "# ECHIDNA v2.0 Advanced Neural Model")
        println(io, "# Training Date: $(Dates.now())")
        println(io, "# Corpus: MAXIMUM (213k+ proofs)")
        println(io, "# Architecture: LSTM with $(size(X, 1)) input features")
        println(io, "# Classes: $(length(prover_labels)) provers")
        println(io, "# Vocabulary: $(vocab.size) words")
        println(io, "# Model Type: neural_network")
    end
    
    @info "✅ Advanced model training complete!"
    @info "  Model saved to: $model_file"
    @info "  Stats saved to: $(joinpath(MODELS_DIR, "advanced_stats.txt"))"
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end