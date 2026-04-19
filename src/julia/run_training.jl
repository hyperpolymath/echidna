# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# run_training.jl — Main entry point for training the ECHIDNA neural solver.
#
# Usage:
#   julia --project=src/julia src/julia/run_training.jl [data_dir] [save_dir]
#
# Defaults:
#   data_dir  = training_data/
#   save_dir  = models/neural/
#
# Environment overrides (see below):
#   ECHIDNA_MAX_PROOF_STATES — cap on proof states loaded (default 200000 on
#     GPU, 50000 on CPU).  Set to 0 to disable the cap and consume the entire
#     expanded corpus; required when re-baselining after corpus growth.
#   ECHIDNA_NUM_EPOCHS      — training epochs (default 30).
#   ECHIDNA_NUM_NEGATIVES   — hard-negative premise samples per example
#     (default 20).
#
# This script:
#   1. Loads JSONL training data (proof states + premises)
#   2. Builds vocabulary from the corpus
#   3. Creates the NeuralSolver (GNN + Transformer)
#   4. Trains with ranking + contrastive loss
#   5. Saves the trained model + vocabulary to save_dir

using Pkg
Pkg.activate(joinpath(@__DIR__))

println("╔═══════════════════════════════════════════════════════════╗")
println("║  ECHIDNA Neural Solver — Training Pipeline               ║")
println("╚═══════════════════════════════════════════════════════════╝")
println()

# Parse arguments
data_dir = length(ARGS) >= 1 ? ARGS[1] : joinpath(@__DIR__, "..", "..", "training_data")
save_dir = length(ARGS) >= 2 ? ARGS[2] : joinpath(@__DIR__, "..", "..", "models", "neural")

println("Data directory: $data_dir")
println("Save directory: $save_dir")
println()

# Load module
println("Loading EchidnaML module...")
include(joinpath(@__DIR__, "EchidnaML.jl"))
using .EchidnaML

# Configure for available hardware
println("Configuring...")
using CUDA, Flux
has_gpu = CUDA.functional()
if has_gpu
    println("  GPU: $(CUDA.device())")
    EchidnaML.set_config!(device=Flux.gpu)
else
    println("  GPU: not available (using CPU)")
    EchidnaML.set_config!(device=Flux.cpu)
end

# Use smaller model dimensions for CPU training
if !has_gpu
    println("  Reducing model size for CPU training")
    EchidnaML.set_config!(
        embedding_dim=128,
        hidden_dim=256,
        num_transformer_layers=2,
        gnn_num_layers=2,
        batch_size=16
    )
end

println("  Embedding dim: $(EchidnaML.get_config().embedding_dim)")
println("  Hidden dim: $(EchidnaML.get_config().hidden_dim)")
println("  Transformer layers: $(EchidnaML.get_config().num_transformer_layers)")
println("  GNN layers: $(EchidnaML.get_config().gnn_num_layers)")
println("  Batch size: $(EchidnaML.get_config().batch_size)")
println()

# Load data
println("═══════════════════════════════════════════════════════════")
println("Loading training data...")
println("═══════════════════════════════════════════════════════════")

# Default cap: 200k on GPU (enough to exercise the expanded corpus without
# OOM on a 24GB card), 50k on CPU (keeps wall-clock finite).  An operator
# re-baselining after corpus growth sets ECHIDNA_MAX_PROOF_STATES=0 to lift
# the cap entirely.
default_cap = has_gpu ? 200_000 : 50_000
cap_env = get(ENV, "ECHIDNA_MAX_PROOF_STATES", "")
max_proof_states = isempty(cap_env) ? default_cap : parse(Int, cap_env)
# `load_training_data` treats any value `<= 0` as "load everything".
cap_label = max_proof_states <= 0 ? "unlimited" : string(max_proof_states)
println("  max_proof_states = $cap_label")

num_negatives = parse(Int, get(ENV, "ECHIDNA_NUM_NEGATIVES", "20"))
println("  num_negatives    = $num_negatives")

train_data, val_data, vocab = load_training_data(data_dir;
    train_split=0.8f0,
    max_proof_states=max_proof_states,
    num_negatives=num_negatives,
)

if isempty(train_data.examples)
    println("ERROR: No training data loaded. Check that JSONL files exist in $data_dir")
    exit(1)
end

println()
println("Vocabulary size: $(vocab.vocab_size)")
println("Training examples: $(length(train_data.examples))")
println("Validation examples: $(length(val_data.examples))")
println()

# Create solver
println("═══════════════════════════════════════════════════════════")
println("Creating NeuralSolver...")
println("═══════════════════════════════════════════════════════════")

solver = create_solver(vocab)
println("Model created successfully")
println()

# Configure training
num_epochs = parse(Int, get(ENV, "ECHIDNA_NUM_EPOCHS", "30"))
training_config = TrainingConfig(
    num_epochs=num_epochs,
    learning_rate=1f-4,
    lr_schedule=:cosine,
    weight_decay=1f-5,
    gradient_clip_norm=1.0f0,
    loss_alpha=0.5f0,
    early_stopping_patience=5,
    checkpoint_every=5,
    eval_every=1,
    save_dir=save_dir
)

# Train
println("═══════════════════════════════════════════════════════════")
println("Training ($(training_config.num_epochs) epochs)...")
println("═══════════════════════════════════════════════════════════")

mkpath(save_dir)
metrics = train_solver!(solver, train_data, val_data; config=training_config)

# Save final model
println()
println("═══════════════════════════════════════════════════════════")
println("Saving final model...")
println("═══════════════════════════════════════════════════════════")

final_path = joinpath(save_dir, "final_model")
save_solver(solver, final_path)

# Save vocabulary separately for the API server
BSON.@save joinpath(save_dir, "vocabulary.bson") vocab

println()
println("╔═══════════════════════════════════════════════════════════╗")
println("║  Training Complete!                                       ║")
println("╚═══════════════════════════════════════════════════════════╝")
println()
println("Model saved to: $save_dir")
println("To start the API server:")
println("  julia --project=src/julia src/julia/run_server.jl $save_dir")
