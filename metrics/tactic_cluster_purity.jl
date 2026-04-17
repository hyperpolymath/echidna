# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# tactic_cluster_purity.jl — Per-prover distinctiveness of tactic
# n-gram profiles. Cheap proxy for clustering on the learned tactic
# embeddings (which requires a trained model; this metric runs
# cold-start).
#
# For each prover, take the top-K tactic-proof bigrams. Compute the
# mean Jaccard distance from every OTHER prover's top-K. Value is the
# median-across-provers of that mean. Higher = more distinctive tactic
# families. Target ≥ 0.65.

module TacticClusterPurity

using ..CorpusLoader: CorpusIndex
using Statistics

export compute, NAME

const NAME = "tactic_cluster_purity"
const TOP_K = 200
const WORD_RE = r"[A-Za-z_][A-Za-z0-9_']*"

function _bigrams(text::AbstractString)::Vector{Tuple{String,String}}
    words = String[]
    for m in eachmatch(WORD_RE, text)
        push!(words, lowercase(m.match))
    end
    [(words[i], words[i+1]) for i in 1:length(words)-1]
end

function _top_bigrams(recs)::Set{Tuple{String,String}}
    counts = Dict{Tuple{String,String}, Int}()
    for r in recs
        for bg in _bigrams(r.tactic_proof)
            counts[bg] = get(counts, bg, 0) + 1
        end
    end
    isempty(counts) && return Set{Tuple{String,String}}()
    sorted = sort(collect(counts); by = x -> -x[2])
    Set(first.(sorted[1:min(TOP_K, length(sorted))]))
end

function _jaccard(a::Set, b::Set)::Float64
    u = length(a ∪ b)
    u == 0 ? 0.0 : 1.0 - length(a ∩ b) / u
end

function compute(idx::CorpusIndex)
    provers = collect(keys(idx))
    profiles = Dict(p => _top_bigrams(idx[p]) for p in provers)
    ranked = [p for p in provers if !isempty(profiles[p])]
    length(ranked) < 2 && return (; value = 0.0, unit = "jaccard_distance",
                                   context = Dict{String, Any}(
                                       "reason" => "not_enough_provers_with_tactics",
                                       "provers_with_tactics" => length(ranked)))

    per_prover = Dict{String, Float64}()
    for p in ranked
        dists = Float64[]
        for q in ranked
            p == q && continue
            push!(dists, _jaccard(profiles[p], profiles[q]))
        end
        per_prover[p] = mean(dists)
    end

    value = median(values(per_prover))
    context = Dict{String, Any}(
        "per_prover"            => per_prover,
        "provers_with_tactics"  => length(ranked),
        "top_k"                 => TOP_K,
        "target"                => 0.65,
    )
    return (; value, unit = "jaccard_distance", context)
end

end
