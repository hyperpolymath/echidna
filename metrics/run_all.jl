#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# run_all.jl — Driver: load corpus, run all eight metrics, POST to
# VeriSimDB, cache JSONL on disk.
#
#   julia --project=src/julia metrics/run_all.jl

using Pkg
const REPO = dirname(dirname(abspath(@__FILE__)))
Pkg.activate(joinpath(REPO, "src", "julia"))

using Dates

include(joinpath(REPO, "metrics", "MetricsSuite.jl"))
using .MetricsSuite

function main()
    training_dir = joinpath(REPO, "training_data")
    fmt = Dates.DateFormat("yyyymmdd-HHMMSS")
    run_id = get(ENV, "METRIC_RUN_ID",
                 "metrics-" * Dates.format(now(), fmt))
    url = get(ENV, "VERISIM_URL", "http://localhost:8080")
    println("run_id     = $run_id")
    println("verisim_url= $url")
    results = run_metrics(training_dir, run_id; verisim_url = url)
    println("Done. ", length(results), " metrics emitted.")
end

main()
