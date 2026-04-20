# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# zipf_s.jl — Fit a Zipf exponent to the theorem-name frequency
# distribution across the full corpus. Rank-frequency slope |s|
# should fall in [0.9, 1.1] for a healthy natural corpus; extreme
# values (>1.3) signal memorisation risk / heavy reuse of
# Mathlib-style prefixes.

module ZipfS

using ..CorpusLoader: CorpusIndex
using Statistics

export compute, NAME

const NAME = "zipf_s"
const HEAD = 1000

function compute(idx::CorpusIndex)
    counts = Dict{String, Int}()
    for (_, recs) in idx
        for r in recs
            isempty(r.theorem) && continue
            counts[r.theorem] = get(counts, r.theorem, 0) + 1
        end
    end
    length(counts) < 100 && return (; value = 0.0, unit = "zipf_s",
                                    context = Dict{String, Any}(
                                        "reason" => "too_few_names",
                                        "unique_names" => length(counts)))

    freqs = sort(collect(values(counts)); rev = true)
    k = min(HEAD, length(freqs))
    xs = log.(1:k)
    ys = log.(Float64.(freqs[1:k]))
    mx, my = mean(xs), mean(ys)
    num = sum((xs .- mx) .* (ys .- my))
    den = sum((xs .- mx) .^ 2)
    slope = den == 0 ? 0.0 : num / den
    s = -slope

    context = Dict{String, Any}(
        "unique_names"  => length(counts),
        "fit_window"    => k,
        "target_low"    => 0.9,
        "target_high"   => 1.1,
    )
    return (; value = s, unit = "zipf_s", context)
end

end
