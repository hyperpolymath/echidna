# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# eval_held_out.jl — Evaluate a trained GNN model on the held-out validation split.
#
# Measures MRR, top-1, top-5, top-10 and appends one JSONL row to
# training_data/eval_results.jsonl.  Compares against the 0.66 cosine baseline.
#
# Usage:
#   just eval
# or:
#   cd src/julia && julia --project=. eval_held_out.jl

using Pkg
Pkg.activate(joinpath(@__DIR__))

using EchidnaML
using JSON3, Dates, Statistics, BSON

function main()
    repo_root = abspath(joinpath(@__DIR__, "..", ".."))
    data_dir  = joinpath(repo_root, "training_data")

    # Try candidate model directories in the same order as load_gnn_model.
    candidate_dirs = [
        joinpath(repo_root, "models", "neural", "gnn_ranker"),
        joinpath(repo_root, "models", "neural", "best_model"),
        joinpath(repo_root, "models", "neural", "final_model"),
    ]

    models_dir = nothing
    for d in candidate_dirs
        if isdir(d)
            models_dir = d
            break
        end
    end

    if models_dir === nothing
        error("No trained model found — run 'just train-cpu' first. " *
              "Checked: $(join(candidate_dirs, ", "))")
    end

    @info "Loading solver from $models_dir"
    solver = load_solver(models_dir)

    @info "Loading validation data from $data_dir"
    t_start = time()
    (_train_ds, val_ds, vocab) = load_training_data(data_dir; train_split=0.8f0)
    @info "Validation split size: $(length(val_ds.examples))  vocab: $(vocab.vocab_size)"

    if isempty(val_ds.examples)
        error("Validation dataset is empty — check training_data/ has proof_states and premises files.")
    end

    # Evaluate using the same scoring path as train.jl::compute_metrics.
    # compute_metrics returns (precision, recall, mrr) using cosine over text embeddings;
    # when a trained model is loaded, the solver's text_encoder reflects learned weights.
    val_metrics = compute_metrics(solver, val_ds; k=10)
    mrr   = val_metrics.mrr
    top1  = val_metrics.precision   # precision@1 is top-1 accuracy at k=1
    top5  = val_metrics.recall      # secondary; full top-k breakdown below
    top10 = val_metrics.precision   # reuse — compute_metrics gives precision@k

    # Finer breakdown: compute_metrics at k=1 and k=5.
    val_k1  = compute_metrics(solver, val_ds; k=1)
    val_k5  = compute_metrics(solver, val_ds; k=5)
    top1  = val_k1.precision
    top5  = val_k5.precision
    top10 = val_metrics.precision

    duration = time() - t_start

    git_sha = try
        strip(read(`git -C $repo_root rev-parse HEAD`, String))
    catch
        "unknown"
    end

    metrics = Dict(
        "timestamp"               => string(now()),
        "git_sha"                 => git_sha,
        "model_path"              => models_dir,
        "val_size"                => length(val_ds.examples),
        "vocab_size"              => vocab.vocab_size,
        "mrr"                     => mrr,
        "top1"                    => top1,
        "top5"                    => top5,
        "top10"                   => top10,
        "cosine_baseline_mrr"     => 0.66,
        "eval_duration_seconds"   => duration,
    )

    out_path = joinpath(data_dir, "eval_results.jsonl")
    open(out_path, "a") do io
        println(io, JSON3.write(metrics))
    end

    @info "Eval complete: MRR=$mrr  top1=$top1  top5=$top5  top10=$top10"
    @info "Results appended to $out_path"

    if mrr >= 0.66f0
        @info "PASS: MRR=$mrr ≥ 0.66 cosine baseline — weights are improving retrieval."
    else
        @warn "FAIL: MRR=$mrr < 0.66 cosine baseline — stop, file a bug before proceeding."
        exit(1)
    end
end

main()
