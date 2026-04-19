# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# prover_floor.jl — Smallest per-prover proof count in the authoritative
# corpus. Drives the 5K-floor strategy: if this value climbs, the
# corpus is getting horizontally broader. Target ≥ 5 000.

module ProverFloor

using ..CorpusLoader: CorpusIndex

export compute, NAME

const NAME = "prover_floor"

function compute(idx::CorpusIndex)
    counts = Dict(p => length(recs) for (p, recs) in idx)
    isempty(counts) && return (; value = 0, unit = "proofs",
                                context = Dict{String, Any}("reason" => "no_provers"))
    floor_val, floor_prover = findmin(counts)
    context = Dict{String, Any}(
        "floor_prover"  => floor_prover,
        "per_prover"    => counts,
        "total_provers" => length(counts),
        "target"        => 5000,
    )
    return (; value = floor_val, unit = "proofs", context)
end

end
