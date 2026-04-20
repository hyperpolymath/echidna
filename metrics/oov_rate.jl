# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# oov_rate.jl — Fraction of corpus tokens NOT in CANON seed.
# Upper bound on the trainer's OOV rate; target ≤ 3 %.

module OOVRate

using ..CorpusLoader: CorpusIndex

export compute, NAME

const NAME = "oov_rate"

const SPLIT_RE = r"[\s\(\)\[\]\{\},;:.\"'`]+"

function _load_canon(path::AbstractString)::Set{String}
    s = Set{String}()
    isfile(path) || return s
    open(path, "r") do fh
        for line in eachline(fh)
            t = strip(line)
            isempty(t) || push!(s, String(t))
        end
    end
    return s
end

function _count_tokens!(acc::Vector{Int}, text::AbstractString, canon::Set{String})
    for raw in split(text, SPLIT_RE; keepempty = false)
        t = String(strip(raw))
        isempty(t) && continue
        acc[1] += 1
        t in canon || (acc[2] += 1)
    end
end

function compute(idx::CorpusIndex;
                 canon_path::AbstractString = joinpath(
                     dirname(dirname(abspath(@__FILE__))),
                     "training_data", "vocabulary_CANON.txt"))
    canon = _load_canon(canon_path)
    acc = Int[0, 0]       # (total, oov)
    per_prover = Dict{String, Tuple{Int, Int}}()

    for (prover, recs) in idx
        before = (acc[1], acc[2])
        for r in recs
            _count_tokens!(acc, r.theorem, canon)
            _count_tokens!(acc, r.goal, canon)
            _count_tokens!(acc, r.tactic_proof, canon)
            for c in r.context
                _count_tokens!(acc, c, canon)
            end
        end
        per_prover[prover] = (acc[1] - before[1], acc[2] - before[2])
    end

    total, oov = acc[1], acc[2]
    value = total == 0 ? 0.0 : oov / total
    context = Dict{String, Any}(
        "total_tokens"  => total,
        "oov_tokens"    => oov,
        "canon_size"    => length(canon),
        "per_prover"    => Dict(p => (t > 0 ? o / t : 0.0)
                                for (p, (t, o)) in per_prover),
        "target"        => 0.03,
    )
    return (; value, unit = "fraction", context)
end

end
