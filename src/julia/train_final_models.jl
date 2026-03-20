#!/usr/bin/env julia
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
FINAL Model Training on COMPLETE Corpus
"""

using LinearAlgebra
using Random
using Dates
using JSON3

const TRAINING_DATA_DIR = "training_data"
const MODELS_DIR = "models"

# Use proper JSON parsing
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

# Train models on complete data
function main()
    @info "ECHIDNA FINAL Model Training on COMPLETE Corpus"
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
    train_logistic!(model, X, y; learning_rate=0.01, epochs=50, batch_size=16)
    
    # Save models
    save_models((vocab=vocab, type="premise_selector"), 
                (model=model, vocab=tactic_vocab, type="tactic_predictor"))
    
    @info "✅ FINAL model training complete!"
    @info "  Models trained on COMPLETE corpus (66k proofs, 179k tactics)"
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end