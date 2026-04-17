#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# vocabulary_canonicalize.jl — Produce a clean canonical seed vocabulary.
#
# vocabulary_UNIFIED.txt and vocabulary_5X.txt are raw-extraction dumps
# from the proof corpora with no filter — they carry obvious junk (short
# letter salads like "aabb", pure-repeat runs, concatenated noise) next to
# real math terms. They are useful as a *survey* of what shows up in
# proofs, but are NOT suitable as a seed for the training tokenizer:
# seeding injects tokens that would otherwise be dropped by the
# min-frequency filter, so any junk in the seed poisons the embedding
# table.
#
# This script builds a curated seed — union of the intentional sources
# only — and applies a minimal sanity filter:
#
#   Sources (curated, in merge order):
#     1. scripts/vocabulary_5x_expansion.jl  (prover/math/proof/typechecker)
#     2. training_data/vocabulary_COMPREHENSIVE.txt
#     3. training_data/vocabulary_FINAL.txt
#     4. training_data/vocabulary_ULTIMATE.txt
#
#   Output:
#     - training_data/vocabulary_CANON.txt
#     - training_data/stats_vocab_canon.json
#
# The raw dumps are NOT ingested; frequency-based vocabulary growth
# happens at training time in src/julia/training/dataloader.jl.
#
# Run:  julia scripts/vocabulary_canonicalize.jl

using JSON3
using Dates

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))

# Bring curated-set builder functions into scope. The guarded-main change
# in vocabulary_5x_expansion.jl prevents side effects on include().
const _CURATED = joinpath(REPO_ROOT, "scripts", "vocabulary_5x_expansion.jl")
isfile(_CURATED) && include(_CURATED)

# ── Junk filter ────────────────────────────────────────────────────────────

"""
    is_valid_token(tok) -> Bool

Drop tokens that are clearly extraction artefacts. Keep long mathlib-style
names (they carry real signal) and Unicode math symbols. Reject:

  * Empty or whitespace-only
  * Length < 2 or > 80
  * Pure digits or pure punctuation
  * Runs of ≥ 4 identical characters anywhere
  * Tokens where > 60 % of characters are a single character
  * Tokens with no letter or non-ASCII math-ish glyph

The 80-char ceiling is generous: Mathlib names up to ~60 chars exist; past
80 is almost always concatenated noise.
"""
function is_valid_token(tok::AbstractString)::Bool
    s = String(strip(tok))
    isempty(s) && return false
    chars = collect(s)
    n = length(chars)
    (n < 2 || n > 80) && return false

    # Reject pure digits / pure punctuation.
    all(isdigit, chars) && return false
    all(c -> !isletter(c) && !isdigit(c), chars) && return false

    # Reject ≥ 3 identical consecutive chars (e.g. "aaa", "---"). Real
    # mathlib identifiers and English/Greek words almost never have a
    # triple-run of the same letter.
    let run = 1, prev = chars[1]
        for c in chars[2:end]
            run = c == prev ? run + 1 : 1
            run >= 3 && return false
            prev = c
        end
    end

    # Reject tokens dominated (> 55 %) by a single character.
    counts = Dict{Char, Int}()
    for c in chars
        counts[c] = get(counts, c, 0) + 1
    end
    maximum(values(counts)) / n > 0.55 && return false

    # Must contain at least one letter (Unicode OK — keeps ∀, λ, ⊥, …).
    any(isletter, chars) || return false

    # Latin-alpha vowel density gate. Tokens whose alphabetic content is
    # purely ASCII Latin must have a vowel ratio ≥ 1/6 — this rejects random
    # consonant-runs ("cdbkzuen…") while preserving mathlib names
    # ("cartesianclosedfunctor…") which always carry English roots.
    letters = [c for c in chars if isletter(c)]
    if !isempty(letters) && all(c -> c in 'a':'z' || c in 'A':'Z', letters)
        vowels = count(c -> lowercase(c) in ('a', 'e', 'i', 'o', 'u', 'y'), letters)
        vowels / length(letters) >= (1 / 6) || return false
        # Also reject any run of >=6 consonants.
        let crun = 0
            for c in letters
                if lowercase(c) in ('a', 'e', 'i', 'o', 'u', 'y')
                    crun = 0
                else
                    crun += 1
                    crun >= 6 && return false
                end
            end
        end
    end

    return true
end

# ── Source loading ─────────────────────────────────────────────────────────

function load_if_exists(path::String)::Set{String}
    out = Set{String}()
    isfile(path) || return out
    open(path, "r") do f
        for line in eachline(f)
            tok = strip(line)
            isempty(tok) || push!(out, String(tok))
        end
    end
    return out
end

function load_curated_sets()::Set{String}
    isdefined(@__MODULE__, :prover_specific_vocabulary) || return Set{String}()
    return union(
        Base.invokelatest(prover_specific_vocabulary),
        Base.invokelatest(deep_mathematics_vocabulary),
        Base.invokelatest(proof_term_vocabulary),
        Base.invokelatest(typechecker_research_vocabulary),
    )
end

# ── Main ───────────────────────────────────────────────────────────────────

function main()
    println("CANONICAL VOCABULARY BUILD")
    println("=" ^ 60)

    td = joinpath(REPO_ROOT, "training_data")

    # Curated sources only. Raw-extraction files (5X, UNIFIED) are
    # surveyed separately below for reporting but NOT merged into the
    # seed vocab — they contain too much junk to bypass the freq filter.
    curated = try
        load_curated_sets()
    catch err
        @warn "Curated-set loader failed" err
        Set{String}()
    end

    sources = Dict{String, Set{String}}(
        "curated_5x"    => curated,
        "COMPREHENSIVE" => load_if_exists(joinpath(td, "vocabulary_COMPREHENSIVE.txt")),
        "FINAL"         => load_if_exists(joinpath(td, "vocabulary_FINAL.txt")),
        "ULTIMATE"      => load_if_exists(joinpath(td, "vocabulary_ULTIMATE.txt")),
    )

    raw_surveyed = Dict{String, Int}(
        "5X_raw"      => length(load_if_exists(joinpath(td, "vocabulary_5X.txt"))),
        "UNIFIED_raw" => length(load_if_exists(joinpath(td, "vocabulary_UNIFIED.txt"))),
    )

    raw_union = Set{String}()
    per_source_raw = Dict{String, Int}()
    for (name, s) in sources
        per_source_raw[name] = length(s)
        union!(raw_union, s)
    end
    println("Sources:")
    for (n, c) in sort(collect(per_source_raw); by = x -> -x[2])
        println("  $(rpad(n, 14)) → $c tokens")
    end
    println("Raw union total: $(length(raw_union))")

    cleaned = Set{String}(t for t in raw_union if is_valid_token(t))
    dropped = length(raw_union) - length(cleaned)
    println("After filter:    $(length(cleaned)) tokens  (dropped $dropped)")

    per_source_kept = Dict(n => length(Set(t for t in s if is_valid_token(t)))
                            for (n, s) in sources)

    out_txt = joinpath(td, "vocabulary_CANON.txt")
    open(out_txt, "w") do f
        for tok in sort(collect(cleaned))
            println(f, tok)
        end
    end
    println("Wrote $out_txt")

    stats = Dict{String, Any}(
        "version"           => "canon-v1",
        "generated_at"      => string(now()),
        "generator"         => "scripts/vocabulary_canonicalize.jl",
        "total_tokens"      => length(cleaned),
        "raw_union_tokens"  => length(raw_union),
        "dropped"           => dropped,
        "per_source_raw"    => per_source_raw,
        "per_source_kept"   => per_source_kept,
        "raw_surveyed_only" => raw_surveyed,
        "filter_rules"      => [
            "2 <= length <= 80",
            "not pure digits / pure punctuation",
            "no run of >=3 identical chars",
            "no single char dominating >55%",
            "must contain at least one letter",
            "ASCII-only tokens: vowel ratio >= 1/6, no >=6 consonant run",
        ],
        "note" => string(
            "CANON is a curated seed. Raw-extraction files (vocabulary_5X.txt, ",
            "vocabulary_UNIFIED.txt) are surveyed but not merged — frequency-based ",
            "vocabulary growth happens at training time in dataloader.jl."
        ),
    )
    out_json = joinpath(td, "stats_vocab_canon.json")
    open(out_json, "w") do f
        JSON3.pretty(f, stats)
    end
    println("Wrote $out_json")

    println("=" ^ 60)
    println("DONE — vocabulary_CANON.txt is the single source of truth.")
end

main()
