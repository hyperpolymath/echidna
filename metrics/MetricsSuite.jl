# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# MetricsSuite.jl — Umbrella module wiring every metric against a
# single corpus pass and a single VeriSimDB sink.

module MetricsSuite

include("corpus_loader.jl")
include("verisim_sink.jl")

using .CorpusLoader: load_corpus, CorpusIndex

include("triangulation_rate.jl")
include("alignment_rate.jl")
include("oov_rate.jl")
include("heaps_beta.jl")
include("tactic_cluster_purity.jl")
include("msc_taxonomy_coverage.jl")
include("prover_floor.jl")
include("zipf_s.jl")

using .VeriSimSink: emit_metric, metric_row
using .TriangulationRate
using .AlignmentRate
using .OOVRate
using .HeapsBeta
using .TacticClusterPurity
using .MSCTaxonomyCoverage
using .ProverFloor
using .ZipfS

export run_metrics, METRIC_MODULES

const METRIC_MODULES = (
    TriangulationRate,
    AlignmentRate,
    OOVRate,
    HeapsBeta,
    TacticClusterPurity,
    MSCTaxonomyCoverage,
    ProverFloor,
    ZipfS,
)

"""
    run_metrics(training_dir, run_id; verisim_url) -> Vector{NamedTuple}

Load the corpus once, run each metric, emit each result to VeriSimDB
(with on-disk fallback). Returns the list of metric rows.
"""
function run_metrics(training_dir::AbstractString,
                     run_id::AbstractString;
                     verisim_url::AbstractString = VeriSimSink.DEFAULT_URL)
    println("Loading corpus from $training_dir …")
    idx = load_corpus(training_dir)
    n_rec = sum(length, values(idx); init = 0)
    println("Loaded $n_rec records across $(length(idx)) provers.")
    results = NamedTuple[]
    for M in METRIC_MODULES
        t0 = time()
        r = M.compute(idx)
        dt = round(time() - t0; digits = 2)
        println("• $(M.NAME) = $(round(r.value; digits = 4))  ($(r.unit), $(dt)s)")
        row = metric_row(run_id, M.NAME, r.value; unit = r.unit, context = r.context)
        emit_metric(row; verisim_url = verisim_url)
        push!(results, (; metric = M.NAME, r.value, r.unit, r.context))
    end
    return results
end

end
