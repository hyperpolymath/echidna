#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# vocabulary_mine_corpus.jl — Mine proof corpora for a frequency-filtered
# identifier vocabulary to complement the hand-curated CANON seed.
#
# Context
# -------
# vocabulary_UNIFIED.txt is a raw frequency dump that carried junk
# (sub-trigrams like "aabb", 100-char letter runs). The CANON seed
# deliberately ignores it. But we still need a way to pick up real
# identifiers — Mathlib theorem names, Isabelle tactic names, Agda
# constructor names, TPTP predicates — that *do* appear in the corpus
# but are missing from the curated lists.
#
# Strategy
# --------
# Walk the per-prover authoritative proof_states_*.jsonl files (the
# same list merge_corpus.jl consumes), tokenise every theorem / goal /
# context entry, count frequencies, apply the same shared filter as
# vocabulary_canonicalize.jl, and keep everything with a count at or
# above `MIN_FREQ`. Frequency is a strong junk filter: random
# extraction artefacts almost never repeat.
#
# Output
# ------
#   training_data/vocabulary_mined.txt
#   training_data/stats_vocab_mined.json
#
# Downstream: vocabulary_canonicalize.jl folds the mined file into the
# CANON seed.
#
# Run:  julia scripts/vocabulary_mine_corpus.jl

using JSON3
using Dates

const REPO_ROOT     = dirname(dirname(abspath(@__FILE__)))
const TRAINING_DIR  = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE   = joinpath(TRAINING_DIR, "vocabulary_mined.txt")
const STATS_FILE    = joinpath(TRAINING_DIR, "stats_vocab_mined.json")

# Share the sanity filter with the canonicalizer.
include(joinpath(REPO_ROOT, "scripts", "vocabulary_canonicalize.jl"))
# The canonicalizer auto-runs its main() on include; that is harmless
# here — it writes the existing CANON, which we'll regenerate downstream.

# Frequency threshold. Tokens that appear at least this many times in
# the combined corpus graduate into the mined vocabulary. 3 is strict
# enough to reject extraction noise while admitting domain-specific
# identifiers that recur across proofs in a family.
const MIN_FREQ = 1

# Hard cap on the mined vocabulary so the final CANON (mined ∪ curated
# ≈ 9K) lands at roughly 100K tokens. After the freq filter, keep the
# top N tokens by descending frequency; the tail is long but
# diminishing-return. Passing 0 disables the cap.
const MAX_MINED = 0

# Per-prover authoritative corpus files — mirrors merge_corpus.jl.
# Aggregate/merged files (UNIFIED, COMPLETE, BALANCED, ULTIMATE, etc.)
# are excluded deliberately to avoid double-counting.
const CORPUS_FILES = [
    "proof_states_mathlib4_max.jsonl",
    "proof_states_coqgym_max.jsonl",
    "proof_states_smtlib.jsonl",
    "proof_states_metamath.jsonl",
    "proof_states_hol_light.jsonl",
    "proof_states_hol4.jsonl",
    "proof_states_acl2.jsonl",
    "proof_states_pvs.jsonl",
    "proof_states_why3.jsonl",
    "proof_states_dafny.jsonl",
    "proof_states_fstar.jsonl",
    "proof_states_idris2.jsonl",
    "proof_states_mizar.jsonl",
    "proof_states_nuprl.jsonl",
    "proof_states_minlog.jsonl",
    "proof_states_twelf.jsonl",
    "proof_states_imandra.jsonl",
    "proof_states_minizinc.jsonl",
    "proof_states_isabelle.jsonl",
    "proof_states_afp.jsonl",
    "proof_states_agda.jsonl",
    "proof_states_tptp.a2ml",
    "proof_states_typechecker_ecosystem.jsonl",
    "proof_states_mathlib4.jsonl",
    "proof_states_coqgym.jsonl",
    "proof_states_2026-03-20.jsonl",
]

# ---------------------------------------------------------------------------
# Tokenisation
# ---------------------------------------------------------------------------

# Same splitter as src/julia/models/encoder.jl:tokenize_text so the mined
# vocabulary matches what the trainer actually sees.
const SPLIT_RE = r"[\s\(\)\[\]\{\},;:.\"'`]+"

"""
    tokenise(text) -> Vector{String}

Split text into candidate tokens. Also splits Agda-style compound
identifiers on a short set of interior delimiters we care about.
"""
function tokenise(text::AbstractString)::Vector{String}
    out = String[]
    for raw in split(text, SPLIT_RE; keepempty = false)
        t = String(strip(raw))
        isempty(t) || push!(out, t)
    end
    return out
end

function fold_record!(counts::Dict{String, Int}, rec::AbstractDict)
    for key in ("theorem", "goal", "tactic_proof")
        if haskey(rec, key) && rec[key] isa AbstractString
            for tok in tokenise(rec[key])
                counts[tok] = get(counts, tok, 0) + 1
            end
        end
    end
    if haskey(rec, "context") && rec["context"] isa AbstractVector
        for item in rec["context"]
            item isa AbstractString || continue
            for tok in tokenise(item)
                counts[tok] = get(counts, tok, 0) + 1
            end
        end
    end
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function mine()
    println("MINE CORPUS VOCABULARY")
    println("=" ^ 60)

    counts = Dict{String, Int}()
    files_seen  = 0
    files_miss  = 0
    records_in  = 0

    for fname in CORPUS_FILES
        path = joinpath(TRAINING_DIR, fname)
        if !isfile(path)
            files_miss += 1
            @info "Skipping absent file" file=fname
            continue
        end
        files_seen += 1
        open(path, "r") do fh
            for line in eachline(fh)
                s = strip(line)
                isempty(s) && continue
                try
                    rec = JSON3.read(s, Dict{String,Any})
                    fold_record!(counts, rec)
                    records_in += 1
                catch
                    # Non-JSON line (e.g. partial a2ml) — ignore.
                end
            end
        end
        println("  + $(rpad(fname, 44))  running unique=$(length(counts))")
    end

    println("Files consumed:   $files_seen  (missing: $files_miss)")
    println("Records ingested: $records_in")
    println("Raw unique tokens: $(length(counts))")

    kept_pairs = Tuple{String, Int}[]
    for (tok, c) in counts
        c >= MIN_FREQ || continue
        is_valid_token(tok) || continue
        push!(kept_pairs, (tok, c))
    end
    n_pre_cap = length(kept_pairs)
    println("After freq>=$MIN_FREQ + filter: $n_pre_cap tokens")

    if MAX_MINED > 0 && length(kept_pairs) > MAX_MINED
        sort!(kept_pairs; by = x -> -x[2])
        kept_pairs = kept_pairs[1:MAX_MINED]
        println("Capped to top $MAX_MINED by frequency.")
    end
    kept = sort!([p[1] for p in kept_pairs])

    open(OUTPUT_FILE, "w") do fh
        for t in kept
            println(fh, t)
        end
    end
    println("Wrote $OUTPUT_FILE")

    stats = Dict{String, Any}(
        "version"           => "mined-v2",
        "generated_at"      => string(now()),
        "generator"         => "scripts/vocabulary_mine_corpus.jl",
        "min_freq"          => MIN_FREQ,
        "max_mined"         => MAX_MINED,
        "files_seen"        => files_seen,
        "files_missing"     => files_miss,
        "records_ingested"  => records_in,
        "raw_unique_tokens" => length(counts),
        "kept_before_cap"   => n_pre_cap,
        "kept_tokens"       => length(kept),
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end
    println("Wrote $STATS_FILE")
    println("=" ^ 60)
end

mine()
