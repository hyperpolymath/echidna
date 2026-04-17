# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# msc_taxonomy_coverage.jl — Approximate coverage of the MSC 2020
# top-level classification using keyword heuristics against theorem
# and goal text. Target ≥ 40 % of MSC top-level codes have ≥ 10 hits.
#
# This is a coarse proxy until proofs are formally tagged with MSC
# codes. The keyword map covers the 63 top-level MSC 2020 classes,
# grouped by what typically appears in mathlib / AFP / Metamath names.

module MSCTaxonomyCoverage

using ..CorpusLoader: CorpusIndex

export compute, NAME

const NAME = "msc_taxonomy_coverage"
const THRESHOLD = 10

# (MSC code, cue patterns). Intentionally conservative — a missing hit
# is preferable to a false positive for coverage reporting.
const MSC_CUES = [
    ("00", ["general", "axiom"]),
    ("01", ["history"]),
    ("03", ["logic", "set", "model", "recursion", "arity", "arity"]),
    ("05", ["combinator", "graph", "matroid", "poset"]),
    ("06", ["lattice", "boolean", "order"]),
    ("08", ["algebra", "variety"]),
    ("11", ["prime", "modular", "dirichlet", "zeta", "arithmetic"]),
    ("12", ["field", "galois", "poly"]),
    ("13", ["commut", "ideal", "ring"]),
    ("14", ["variety", "scheme", "algebraic_geom"]),
    ("15", ["matrix", "linear", "det", "eigen"]),
    ("16", ["module", "noncomm"]),
    ("17", ["lie", "jordan_alg"]),
    ("18", ["category", "functor", "topos", "yoneda", "adjoin"]),
    ("19", ["ktheory"]),
    ("20", ["group", "sylow", "abelian"]),
    ("22", ["topological_group", "liegroup"]),
    ("26", ["real", "calculus", "derivative", "integral"]),
    ("28", ["measure", "integrable", "nullset"]),
    ("30", ["complex", "holomorph", "meromorph"]),
    ("31", ["potential"]),
    ("32", ["severalcomplex"]),
    ("33", ["specialfn"]),
    ("34", ["ode"]),
    ("35", ["pde"]),
    ("37", ["dynamical", "ergodic"]),
    ("39", ["functional_eq"]),
    ("40", ["series", "summable"]),
    ("41", ["approx"]),
    ("42", ["fourier", "harmonic"]),
    ("43", ["abstractharmonic"]),
    ("44", ["laplace", "integral_transform"]),
    ("45", ["integral_eq"]),
    ("46", ["banach", "hilbert", "normed"]),
    ("47", ["operator"]),
    ("49", ["variational"]),
    ("51", ["incidence", "euclid"]),
    ("52", ["convex", "polytope"]),
    ("53", ["riemann", "differentialgeom", "curvature"]),
    ("54", ["topolog", "continuous_fn"]),
    ("55", ["homotopy", "homolog"]),
    ("57", ["manifold", "knot"]),
    ("58", ["globalanalysis"]),
    ("60", ["probab", "martingale"]),
    ("62", ["statistic"]),
    ("65", ["numeric"]),
    ("68", ["algorithm", "computation"]),
    ("70", ["mechanic"]),
    ("74", ["elastic", "material"]),
    ("76", ["fluid"]),
    ("78", ["electromag"]),
    ("80", ["thermodyn"]),
    ("81", ["quantum"]),
    ("82", ["statmech"]),
    ("83", ["relativity", "gravit"]),
    ("85", ["astronom"]),
    ("86", ["geophysic"]),
    ("90", ["operations_research", "mdp"]),
    ("91", ["gametheory", "economic"]),
    ("92", ["biolog", "epidem"]),
    ("93", ["control_theory"]),
    ("94", ["information_theory", "coding"]),
    ("97", ["education"]),
]

const TOTAL_CLASSES = length(MSC_CUES)

function compute(idx::CorpusIndex)
    counts = Dict(code => 0 for (code, _) in MSC_CUES)
    for (_, recs) in idx
        for r in recs
            blob = lowercase(string(r.theorem, " ", r.goal, " ",
                                    join(r.context, " ")))
            for (code, cues) in MSC_CUES
                for cue in cues
                    if occursin(cue, blob)
                        counts[code] += 1
                        break
                    end
                end
            end
        end
    end

    covered = count(v -> v >= THRESHOLD, values(counts))
    value = covered / TOTAL_CLASSES
    context = Dict{String, Any}(
        "covered_classes"   => covered,
        "total_classes"     => TOTAL_CLASSES,
        "threshold"         => THRESHOLD,
        "per_class_counts"  => counts,
        "target"            => 0.40,
    )
    return (; value, unit = "fraction", context)
end

end
