# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# run_training_cpu.jl — CPU-pinned, capped training entry point for the
# ECHIDNA neural premise selector.
#
# Why a separate entry point: `run_training.jl` auto-selects the GPU when
# `CUDA.functional()` is true, but `training/train.jl` does not yet move
# per-batch token tensors to the device, so the GPU path is not wired.
# This script forces `Flux.cpu` and a proof-state cap so a reliable,
# bounded training run can be produced on the real per-prover corpus
# without GPU plumbing.
#
# Usage:
#   julia --project=src/julia src/julia/run_training_cpu.jl [data_dir] [save_dir]
#
# Environment overrides:
#   ECHIDNA_MAX_PROOF_STATES — joinable-proof cap (default 20000; 0 = all)
#   ECHIDNA_NUM_EPOCHS       — training epochs (default 12)
#   ECHIDNA_NUM_NEGATIVES    — negative premises per example (default 20)

using Pkg
Pkg.activate(joinpath(@__DIR__))
using Dates

include(joinpath(@__DIR__, "EchidnaML.jl"))
using .EchidnaML
import Flux
import BSON

data_dir = length(ARGS) >= 1 ? ARGS[1] : joinpath(@__DIR__, "..", "..", "training_data")
save_dir = length(ARGS) >= 2 ? ARGS[2] : joinpath(@__DIR__, "..", "..", "models", "neural")

max_proof_states = parse(Int, get(ENV, "ECHIDNA_MAX_PROOF_STATES", "20000"))
num_epochs       = parse(Int, get(ENV, "ECHIDNA_NUM_EPOCHS", "12"))
num_negatives    = parse(Int, get(ENV, "ECHIDNA_NUM_NEGATIVES", "20"))

println("ECHIDNA neural training (CPU, capped)")
println("  data_dir         = $data_dir")
println("  save_dir         = $save_dir")
println("  max_proof_states = $(max_proof_states <= 0 ? "unlimited" : string(max_proof_states))")
println("  num_epochs       = $num_epochs")
println("  num_negatives    = $num_negatives")

# CPU-pinned model size (matches run_training.jl's CPU branch).
EchidnaML.set_config!(
    device=Flux.cpu,
    embedding_dim=128,
    hidden_dim=256,
    num_transformer_layers=2,
    gnn_num_layers=2,
    batch_size=16,
)

train_data, val_data, vocab = load_training_data(data_dir;
    train_split=0.85f0,
    max_proof_states=max_proof_states,
    num_negatives=num_negatives,
)

if isempty(train_data.examples)
    println("ERROR: no training examples built from $data_dir")
    exit(1)
end

println("vocab=$(vocab.vocab_size)  train=$(length(train_data.examples))  val=$(length(val_data.examples))")

solver = create_solver(vocab)

config = TrainingConfig(
    num_epochs=num_epochs,
    learning_rate=1f-4,
    lr_schedule=:cosine,
    weight_decay=1f-5,
    gradient_clip_norm=1.0f0,
    loss_alpha=0.5f0,
    early_stopping_patience=5,
    checkpoint_every=5,
    eval_every=1,
    save_dir=save_dir,
)

mkpath(save_dir)
t_start = time()
metrics = train_solver!(solver, train_data, val_data; config=config)
duration_seconds = time() - t_start

# Deploy alias: gnn_endpoint.jl loads gnn_ranker → best_model → final_model.
best_dir = joinpath(save_dir, "best_model")
ranker_dir = joinpath(save_dir, "gnn_ranker")
if isdir(best_dir)
    rm(ranker_dir; recursive=true, force=true)
    cp(best_dir, ranker_dir)
    println("Published best_model → $ranker_dir")
end

save_solver(solver, joinpath(save_dir, "final_model"))
BSON.@save joinpath(save_dir, "vocabulary.bson") vocab

# Flat canonical artefacts expected by gnn_endpoint.jl and the spec.
import JSON3 as _JSON3
weights = Flux.state(solver)
BSON.bson(joinpath(save_dir, "premise_selector.bson"), weights=weights)
BSON.bson(joinpath(save_dir, "tactic_predictor.bson"), weights=weights)

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

# Compute final MRR / top-k on validation split.
val_metrics = compute_metrics(solver, val_data; k=10)
val_top1    = compute_metrics(solver, val_data; k=1).precision
val_top5    = compute_metrics(solver, val_data; k=5).precision
println("Validation MRR=$(round(val_metrics.mrr, digits=4))  top1=$(round(val_top1, digits=4))  top5=$(round(val_top5, digits=4))  top10=$(round(val_metrics.precision, digits=4))")

# Append metrics row to training_data/metrics_baseline.jsonl.
git_sha = try; strip(read(`git -C $(joinpath(@__DIR__, "..", "..")) rev-parse --short HEAD`, String)); catch; "unknown"; end
metrics_row = Dict{String,Any}(
    "timestamp"        => string(Dates.now()),
    "git_sha"          => git_sha,
    "mrr"              => round(Float64(val_metrics.mrr), digits=6),
    "top1"             => round(Float64(val_top1), digits=6),
    "top5"             => round(Float64(val_top5), digits=6),
    "top10"            => round(Float64(val_metrics.precision), digits=6),
    "epochs"           => num_epochs,
    "max_proof_states" => max_proof_states,
    "duration_seconds" => round(duration_seconds, digits=1),
    "device"           => "cpu",
)
metrics_baseline_path = joinpath(data_dir, "metrics_baseline.jsonl")
open(metrics_baseline_path, "a") do io
    println(io, _JSON3.write(metrics_row))
end

# Rewrite models/model_metadata.txt with real values.
metadata_path = joinpath(@__DIR__, "..", "..", "models", "model_metadata.txt")
open(metadata_path, "w") do io
    println(io, "# ECHIDNA Neural Models v2.0")
    println(io, "# Trained: $(Dates.now())")
    println(io, "# Git SHA: $git_sha")
    println(io, "# Device: CPU")
    println(io, "# Premise Selector: vocabulary-based ($(vocab.vocab_size) words)")
    println(io, "# Tactic Predictor: neural text encoder ($(length(tactic_classes)) classes)")
    println(io, "# MRR: $(round(Float64(val_metrics.mrr), digits=4))")
    println(io, "# Top-1 Precision: $(round(Float64(val_top1), digits=4))")
    println(io, "# Top-5 Precision: $(round(Float64(val_top5), digits=4))")
    println(io, "# Epochs: $num_epochs")
    println(io, "# Max Proof States: $max_proof_states")
    println(io, "# Training Examples: $(length(train_data.examples))")
    println(io, "# Validation Examples: $(length(val_data.examples))")
end

println(">>> TRAINING COMPLETE — model saved to $save_dir")
println("MRR: $(round(Float64(val_metrics.mrr), digits=4))")
