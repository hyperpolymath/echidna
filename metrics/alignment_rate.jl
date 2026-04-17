# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# alignment_rate.jl — Fraction of theorems whose normalised name is
# shared by ≥ 2 provers, weighted by cross-prover-pair count.
#
# Informally: how many RDF sameAs-edges could the VeriSim graph carry
# today? Target ≥ 30 % of theorems appear in at least one alignment.

module AlignmentRate

using ..CorpusLoader: CorpusIndex
using ..TriangulationRate: _norm

export compute, NAME

const NAME = "alignment_rate"

function compute(idx::CorpusIndex)
    by_name = Dict{String, Set{String}}()
    for (prover, recs) in idx
        for r in recs
            isempty(r.theorem) && continue
            n = _norm(r.theorem)
            isempty(n) && continue
            push!(get!(by_name, n, Set{String}()), prover)
        end
    end

    total = length(by_name)
    aligned_names = 0
    pair_edges    = 0
    for s in values(by_name)
        k = length(s)
        if k >= 2
            aligned_names += 1
            pair_edges    += (k * (k - 1)) ÷ 2
        end
    end

    value = total == 0 ? 0.0 : aligned_names / total
    context = Dict{String, Any}(
        "total_unique_names"  => total,
        "aligned_names"       => aligned_names,
        "prover_pair_edges"   => pair_edges,
        "target"              => 0.30,
    )
    return (; value, unit = "fraction", context)
end

end
