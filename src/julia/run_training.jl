# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# run_training.jl — Main entry point for training the ECHIDNA neural solver.
#
# Usage:
#   julia --project=src/julia src/julia/run_training.jl [data_dir] [save_dir] \
#       [--corpus-json a.json,b.json] [--synonyms-dir DIR] [--prover lean]
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
# Saturation-campaign flags (2026-06-01):
#   --corpus-json A,B,C   Comma-separated paths to Corpus JSON files emitted
#                         by Rust corpus adapters (e.g. data/corpus/lean.json).
#                         Their rows are unioned with whatever
#                         load_training_data returns. Hazard-flagged entries
#                         (any axiom_usage flag set) are dropped.
#   --synonyms-dir DIR    Directory containing per-prover + cross-prover
#                         synonym TOMLs. Defaults to data/synonyms.
#   --prover P            Prover symbol to attach to corpus rows when
#                         translating to TrainingExample (default: lean).
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

# Parse arguments: positional (data_dir, save_dir) preserved for back-compat;
# saturation-campaign flags (--corpus-json, --synonyms-dir, --prover) are
# extracted from ARGS before the positional read so order is not enforced.
function _extract_flag!(args::Vector{String}, name::String,
                        default::String)::String
    i = findfirst(==(name), args)
    if i === nothing
        return default
    end
    if i == length(args)
        @warn "$name flag passed without a value; using default" default
        deleteat!(args, i)
        return default
    end
    val = args[i + 1]
    deleteat!(args, i:i + 1)
    return val
end

_argv = copy(ARGS)
corpus_json_arg  = _extract_flag!(_argv, "--corpus-json",  "")
synonyms_dir_arg = _extract_flag!(_argv, "--synonyms-dir", joinpath(@__DIR__, "..", "..", "data", "synonyms"))
prover_arg       = _extract_flag!(_argv, "--prover",       "lean")

data_dir = length(_argv) >= 1 ? _argv[1] : joinpath(@__DIR__, "..", "..", "training_data")
save_dir = length(_argv) >= 2 ? _argv[2] : joinpath(@__DIR__, "..", "..", "models", "neural")

println("Data directory: $data_dir")
println("Save directory: $save_dir")
println()

# Load module
println("Loading EchidnaML module...")
include(joinpath(@__DIR__, "EchidnaML.jl"))
using .EchidnaML

# Saturation-campaign corpus + synonym helpers (PR #198).
include(joinpath(@__DIR__, "corpus_loader.jl"))
using .CorpusLoader
include(joinpath(@__DIR__, "saturation_synonyms.jl"))
using .SaturationSynonyms

"""
    load_corpus_examples(corpus_paths, prover_kind, synonyms_dir)

Read one or more Corpus JSON files (saturation-campaign Rust adapter
output), translate to `TrainingExample` rows. Hazard-filtered: entries
with any `axiom_usage` flag set are dropped, matching the SA
design-search reject convention in `src/rust/corpus/mod.rs`.

The `discipline_tags` field of each emitted `TrainingExample` is
populated from `CorpusLoader.entry_disciplines(entry)`, sourced from
`axiom_usage.other` strings prefixed with `discipline:`. Cross-prover
synonym tables are pre-loaded for future feature-lookup paths
(downstream consumer in `training/train.jl` may concatenate
`discipline_feature_vector` onto goal embeddings; this PR ships the
data path only).
"""
function load_corpus_examples(corpus_paths::Vector{String},
                              prover_kind::Symbol,
                              synonyms_dir::String)
    isempty(corpus_paths) && return TrainingExample[]

    # Pre-load cross-prover vocab tables (currently consumed downstream;
    # called here so any TOML breakage surfaces at training-launch time,
    # not mid-epoch).
    try
        SaturationSynonyms.load_msc2020(synonyms_dir)
    catch e
        @warn "load_msc2020 failed (continuing with empty table)" exception=e
    end

    examples = TrainingExample[]
    for path in corpus_paths
        isfile(path) || (@warn "corpus JSON not found, skipping" path; continue)
        corpus = CorpusLoader.load_corpus_json(path)
        rows   = CorpusLoader.corpus_to_training_examples(corpus, prover_kind)

        for (entry, row) in zip(corpus.entries, rows)
            # Hazard gate (matches Rust SA reject convention).
            hz = row.hazards
            has_hazard = false
            if hz isa AbstractDict
                for (k, v) in hz
                    k == "other" && continue
                    if v isa Bool && v
                        has_hazard = true
                        break
                    end
                end
            end
            has_hazard && continue

            prover = safe_parse_prover(string(prover_kind))
            prover === nothing && continue

            ps = ProofState(
                prover,
                row.proof_state_fields.goal,
                row.proof_state_fields.context,
                row.proof_state_fields.hypotheses,
                row.proof_state_fields.available_premises,
                row.proof_state_fields.proof_depth,
                row.proof_state_fields.metadata,
            )

            premises = Premise[]
            for p in row.candidate_premise_field_rows
                push!(premises, Premise(p.name, p.statement, prover,
                                        nothing, p.frequency_score,
                                        p.relevance_score))
            end

            disciplines = CorpusLoader.entry_disciplines(entry)

            push!(examples, TrainingExample(ps, premises,
                                            row.relevant_indices, prover,
                                            disciplines))
        end
    end

    @info "load_corpus_examples produced $(length(examples)) TrainingExample rows from $(length(corpus_paths)) corpus file(s)" prover_kind synonyms_dir
    return examples
end

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

# Saturation-campaign corpus inputs (optional). Translate each Corpus JSON
# into TrainingExample rows and union them onto the JSONL-derived train
# split. Validation split is left untouched — corpus-sourced rows are
# treated as training-only signal in this first wiring; held-out evaluation
# remains on the canonical JSONL split.
if !isempty(corpus_json_arg)
    corpus_paths = String.(split(corpus_json_arg, ","))
    filter!(!isempty, corpus_paths)
    if !isempty(corpus_paths)
        prover_sym = Symbol(prover_arg)
        @info "Loading saturation-campaign corpus inputs" corpus_paths prover_sym synonyms_dir_arg
        extra_examples = load_corpus_examples(corpus_paths, prover_sym, synonyms_dir_arg)
        if !isempty(extra_examples)
            append!(train_data.examples, extra_examples)
            @info "Unioned $(length(extra_examples)) corpus-derived examples into train split" total=length(train_data.examples)
        end
    end
end

if isempty(train_data.examples)
    println("ERROR: No training data loaded. Check that JSONL files exist in $data_dir, " *
            "or pass --corpus-json a.json,b.json for saturation-campaign inputs.")
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
