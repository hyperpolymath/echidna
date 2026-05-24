# SPDX-License-Identifier: MPL-2.0
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
using Dates

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
t_start = time()
metrics = train_solver!(solver, train_data, val_data; config=training_config)
duration_seconds = time() - t_start

# Save final model
println()
println("═══════════════════════════════════════════════════════════")
println("Saving final model...")
println("═══════════════════════════════════════════════════════════")

final_path = joinpath(save_dir, "final_model")
save_solver(solver, final_path)

# Deploy alias: gnn_endpoint.jl loads gnn_ranker → best_model → final_model.
best_dir = joinpath(save_dir, "best_model")
ranker_dir = joinpath(save_dir, "gnn_ranker")
if isdir(best_dir)
    rm(ranker_dir; recursive=true, force=true)
    cp(best_dir, ranker_dir)
    println("Published best_model → $ranker_dir")
end

# Save vocabulary separately for the API server
BSON.@save joinpath(save_dir, "vocabulary.bson") vocab

# Flat canonical artefacts expected by gnn_endpoint.jl and the spec.
# premise_selector.bson = the full NeuralSolver weights (renamed for clarity).
# tactic_predictor.bson = same weights (tactic side shares the text_encoder).
# vocab.json = human-readable vocabulary for inspection and version checks.
import JSON3 as _JSON3
weights = Flux.state(solver)
BSON.bson(joinpath(save_dir, "premise_selector.bson"), weights=weights)
BSON.bson(joinpath(save_dir, "tactic_predictor.bson"), weights=weights)

# Build a compact vocab.json: token→id map + metadata.
tactic_classes = sort(unique([
    ex.proof_state.goal[1:min(8,length(ex.proof_state.goal))]
    for ex in vcat(train_data.examples, val_data.examples)
]))
vocab_json = Dict(
    "vocab_size"     => vocab.vocab_size,
    "tactic_classes" => length(tactic_classes),
    "token_to_id"    => vocab.token_to_id,
)
open(joinpath(save_dir, "vocab.json"), "w") do io
    _JSON3.write(io, vocab_json)
end
println("Saved vocab.json ($(vocab.vocab_size) tokens, $(length(tactic_classes)) tactic classes)")

# Compute final MRR / top-k on validation split.
val_metrics = compute_metrics(solver, val_data; k=10)
val_top1    = compute_metrics(solver, val_data; k=1).precision
val_top5    = compute_metrics(solver, val_data; k=5).precision
println("Validation MRR=$(round(val_metrics.mrr, digits=4))  top1=$(round(val_top1, digits=4))  top5=$(round(val_top5, digits=4))  top10=$(round(val_metrics.precision, digits=4))")

# Append a single JSONL row to training_data/metrics_baseline.jsonl.
git_sha = try; strip(read(`git -C $(joinpath(@__DIR__, "..", "..")) rev-parse --short HEAD`, String)); catch; "unknown"; end
metrics_row = Dict{String,Any}(
    "timestamp"        => string(Dates.now()),
    "git_sha"          => git_sha,
    "mrr"              => round(Float64(val_metrics.mrr), digits=6),
    "top1"             => round(Float64(val_top1), digits=6),
    "top5"             => round(Float64(val_top5), digits=6),
    "top10"            => round(Float64(val_metrics.precision), digits=6),
    "epochs"           => training_config.num_epochs,
    "max_proof_states" => max_proof_states,
    "duration_seconds" => round(duration_seconds, digits=1),
    "device"           => has_gpu ? "gpu" : "cpu",
)
metrics_baseline_path = joinpath(data_dir, "metrics_baseline.jsonl")
open(metrics_baseline_path, "a") do io
    println(io, _JSON3.write(metrics_row))
end
println("Appended metrics row to $metrics_baseline_path")

# Rewrite models/model_metadata.txt with real values.
metadata_path = joinpath(@__DIR__, "..", "..", "models", "model_metadata.txt")
open(metadata_path, "w") do io
    println(io, "# ECHIDNA Neural Models v2.0")
    println(io, "# Trained: $(Dates.now())")
    println(io, "# Git SHA: $git_sha")
    println(io, "# Device: $(has_gpu ? "GPU" : "CPU")")
    println(io, "# Premise Selector: vocabulary-based ($(vocab.vocab_size) words)")
    println(io, "# Tactic Predictor: neural text encoder ($(length(tactic_classes)) classes)")
    println(io, "# MRR: $(round(Float64(val_metrics.mrr), digits=4))")
    println(io, "# Top-1 Precision: $(round(Float64(val_top1), digits=4))")
    println(io, "# Top-5 Precision: $(round(Float64(val_top5), digits=4))")
    println(io, "# Epochs: $(training_config.num_epochs)")
    println(io, "# Max Proof States: $max_proof_states")
    println(io, "# Training Examples: $(length(train_data.examples))")
    println(io, "# Validation Examples: $(length(val_data.examples))")
end
println("Updated $metadata_path")

println()
println("╔═══════════════════════════════════════════════════════════╗")
println("║  Training Complete!                                       ║")
println("╚═══════════════════════════════════════════════════════════╝")
println()
println("Model saved to: $save_dir")
println("MRR: $(round(Float64(val_metrics.mrr), digits=4))")
println("To start the API server:")
println("  julia --project=src/julia src/julia/run_server.jl $save_dir")
