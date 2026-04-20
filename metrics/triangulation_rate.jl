# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# triangulation_rate.jl — Fraction of theorems (by normalised name) that
# have proofs in ≥ 3 independent prover backends. Target ≥ 15 %.

module TriangulationRate

using ..CorpusLoader: CorpusIndex

export compute, NAME

const NAME = "triangulation_rate"

# Conservative normaliser: lower-case, strip non-alphanumeric, drop
# prover-specific prefixes (Mathlib's `Mathlib.Algebra.` etc.).
function _norm(name::AbstractString)
    s = lowercase(String(name))
    s = replace(s, r"[^a-z0-9_]" => "_")
    # Trim leading dotted namespace segments that survive as underscores.
    s = replace(s, r"^[a-z]+_+" => "")
    return strip(s, '_')
end

function compute(idx::CorpusIndex)
    by_name = Dict{String, Set{String}}()
    for (prover, recs) in idx
        for r in recs
            isempty(r.theorem) && continue
            n = _norm(r.theorem)
            isempty(n) && continue
            provers = get!(by_name, n, Set{String}())
            push!(provers, prover)
        end
    end

    total = length(by_name)
    triangulated = count(p -> length(p) >= 3, values(by_name))
    cross2 = count(p -> length(p) >= 2, values(by_name))

    value = total == 0 ? 0.0 : triangulated / total
    context = Dict{String, Any}(
        "total_unique_names"  => total,
        "cross_2_plus"        => cross2,
        "cross_3_plus"        => triangulated,
        "target"              => 0.15,
    )
    return (; value, unit = "fraction", context)
end

end
