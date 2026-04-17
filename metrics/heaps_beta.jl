# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# heaps_beta.jl — Fit Heap's law V ≈ k · N^β on the flattened corpus.
# Target β ∈ [0.55, 0.70] for identifier-heavy proof text.
#
# Method: sample token stream in log-spaced checkpoints, count unique
# tokens seen so far, least-squares fit log V vs log N.

module HeapsBeta

using ..CorpusLoader: CorpusIndex
using Statistics

export compute, NAME

const NAME = "heaps_beta"
const SPLIT_RE = r"[\s\(\)\[\]\{\},;:.\"'`]+"

function _flatten(idx::CorpusIndex)
    out = String[]
    for recs in values(idx), r in recs
        for raw in split(string(r.theorem, " ", r.goal, " ", r.tactic_proof,
                                " ", join(r.context, " ")),
                          SPLIT_RE; keepempty = false)
            t = String(strip(raw))
            isempty(t) || push!(out, t)
        end
    end
    return out
end

function _checkpoints(n::Int)::Vector{Int}
    n <= 1 && return Int[n]
    ks = Int[]
    k = 100
    while k < n
        push!(ks, k)
        k = Int(round(k * 1.5))
    end
    push!(ks, n)
    return ks
end

function compute(idx::CorpusIndex)
    toks = _flatten(idx)
    n = length(toks)
    n < 200 && return (; value = 0.0, unit = "beta",
                       context = Dict{String, Any}("reason" => "too_few_tokens",
                                                   "total_tokens" => n))

    seen = Set{String}()
    xs = Float64[]
    ys = Float64[]
    ckpts = _checkpoints(n)
    ci = 1
    for (i, t) in enumerate(toks)
        push!(seen, t)
        if ci <= length(ckpts) && i == ckpts[ci]
            push!(xs, log(i))
            push!(ys, log(length(seen)))
            ci += 1
        end
    end

    # Least-squares slope of log V ~ β · log N + log k.
    mx, my = mean(xs), mean(ys)
    num = sum((xs .- mx) .* (ys .- my))
    den = sum((xs .- mx) .^ 2)
    β = den == 0 ? 0.0 : num / den
    log_k = my - β * mx

    context = Dict{String, Any}(
        "total_tokens"   => n,
        "unique_tokens"  => length(seen),
        "k"              => exp(log_k),
        "checkpoints"    => length(xs),
        "target_low"     => 0.55,
        "target_high"    => 0.70,
    )
    return (; value = β, unit = "beta", context)
end

end
