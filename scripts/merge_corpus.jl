#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# merge_corpus.jl -- Merge all ECHIDNA corpus extraction results into a unified
# training file. Reads per-prover proof_states_*.jsonl files, deduplicates by
# (prover, theorem) pair (keeping the entry with richer context), assigns fresh
# sequential IDs, and writes:
#   - training_data/proof_states_UNIFIED.jsonl   (deduplicated corpus)
#   - training_data/stats_UNIFIED.json           (summary statistics)
#   - training_data/vocabulary_UNIFIED.txt        (vocabulary from goals/theorems)

using JSON3
using Dates

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const TRAINING_DIR = joinpath(dirname(dirname(abspath(@__FILE__))), "training_data")

# Per-prover source files -- the authoritative extractions.
# We list them explicitly to avoid pulling in aggregate/merged files
# (ABSOLUTE_COMPLETE, ULTIMATE, FINAL_BALANCED, COMPLETE, all, v2, etc.).
const PER_PROVER_FILES = [
    "proof_states_mathlib4_max.jsonl",   # Lean 4 / mathlib4 (113K)
    "proof_states_coqgym_max.jsonl",     # Coq (15K)
    "proof_states_smtlib.jsonl",         # Z3/CVC5/Alt-Ergo (20K)
    "proof_states_metamath.jsonl",       # Metamath (47K)
    "proof_states_hol_light.jsonl",      # HOL Light (7K)
    "proof_states_hol4.jsonl",           # HOL4 (1.9K)
    "proof_states_acl2.jsonl",           # ACL2
    "proof_states_pvs.jsonl",            # PVS
    "proof_states_why3.jsonl",           # Why3
    "proof_states_dafny.jsonl",          # Dafny
    "proof_states_fstar.jsonl",          # F*
    "proof_states_idris2.jsonl",         # Idris2
    "proof_states_mizar.jsonl",          # Mizar
    "proof_states_nuprl.jsonl",          # Nuprl (synthetic)
    "proof_states_minlog.jsonl",         # Minlog (synthetic)
    "proof_states_twelf.jsonl",          # Twelf (synthetic)
    "proof_states_imandra.jsonl",        # Imandra (synthetic)
    "proof_states_minizinc.jsonl",       # MiniZinc / constraint solvers
    "proof_states_mathlib4.jsonl",       # Additional mathlib4 (smaller set)
    "proof_states_coqgym.jsonl",         # Additional CoqGym (smaller set)
    "proof_states_2026-03-20.jsonl",     # Dated snapshot
]

# The 30 prover backends ECHIDNA supports.
const ALL_PROVERS = Set([
    "Lean", "Lean4", "Coq", "Rocq", "Agda", "Isabelle", "Idris2", "Fstar", "F*",
    "Z3", "CVC5", "CVC4", "Alt-Ergo", "AltErgo",
    "Dafny", "Why3",
    "Metamath", "HOLLight", "HOL Light", "Mizar", "HOL4", "PVS", "ACL2",
    "TLAPS", "Twelf", "Nuprl", "Minlog", "Imandra",
    "Vampire", "EProver", "E Prover", "SPASS",
    "GLPK", "SCIP", "MiniZinc", "Chuffed", "ORTools", "OR-Tools",
])

# Canonical prover name mapping (normalise variants).
const PROVER_CANONICAL = Dict(
    "Lean4" => "Lean",
    "Rocq" => "Coq",
    "Fstar" => "F*",
    "CVC4" => "CVC5",
    "AltErgo" => "Alt-Ergo",
    "HOL Light" => "HOLLight",
    "E Prover" => "EProver",
    "OR-Tools" => "ORTools",
)

# Total expected backend count for coverage calculation.
const TOTAL_BACKENDS = 30

"""
    canonical_prover(name::String) -> String

Return the canonical prover name for deduplication.
"""
function canonical_prover(name::String)::String
    return get(PROVER_CANONICAL, name, name)
end

"""
    context_richness(entry::Dict) -> Int

Score how rich the context of a proof entry is.
Higher is better -- used to pick the best duplicate.
"""
function context_richness(entry::Dict)::Int
    score = 0
    goal = get(entry, "goal", "")
    score += length(string(goal))
    ctx = get(entry, "context", [])
    if ctx isa AbstractVector
        score += sum(length(string(c)) for c in ctx; init=0)
    end
    tp = get(entry, "tactic_proof", nothing)
    if tp !== nothing
        score += length(string(tp)) * 2
    end
    ps = get(entry, "proof_steps", nothing)
    if ps !== nothing
        score += Int(ps) * 5
    end
    if get(entry, "proof_type", nothing) !== nothing
        score += 10
    end
    if get(entry, "logic", nothing) !== nothing
        score += 10
    end
    return score
end

"""
    load_jsonl(filepath::String) -> Vector{Dict{String,Any}}

Load a JSONL file, skipping malformed lines.
"""
function load_jsonl(filepath::String)::Vector{Dict{String,Any}}
    entries = Dict{String,Any}[]
    if !isfile(filepath)
        return entries
    end
    for (lineno, line) in enumerate(eachline(filepath))
        stripped = strip(line)
        isempty(stripped) && continue
        try
            entry = Dict{String,Any}(pairs(JSON3.read(stripped)))
            push!(entries, entry)
        catch
            println("  WARN: Skipped malformed JSON at $(basename(filepath)):$lineno")
        end
    end
    return entries
end

"""
    extract_words(text::String) -> Set{String}

Extract alphabetic tokens from text for vocabulary building.
Split on non-alphanumeric, keep tokens >= 3 chars that are alphabetic.
"""
function extract_words(text::String)::Set{String}
    tokens = split(text, r"[^a-zA-Z]+")
    return Set(lowercase(t) for t in tokens if length(t) >= 3 && all(isalpha, t))
end

function main()::Int
    println("=" ^ 70)
    println("ECHIDNA Corpus Merge -- merge_corpus.jl")
    println("=" ^ 70)

    # ------------------------------------------------------------------
    # 1. Load all per-prover files
    # ------------------------------------------------------------------
    all_entries = Dict{String,Any}[]
    file_counts = Dict{String,Int}()

    for fname in PER_PROVER_FILES
        fpath = joinpath(TRAINING_DIR, fname)
        entries = load_jsonl(fpath)
        file_counts[fname] = length(entries)
        if !isempty(entries)
            println("  Loaded $(lpad(string(length(entries)), 7)) proofs from $fname")
        else
            println("  SKIP   $fname (not found or empty)")
        end
        append!(all_entries, entries)
    end

    println("\nTotal raw entries loaded: $(length(all_entries))")

    # ------------------------------------------------------------------
    # 2. Deduplicate by (canonical_prover, theorem)
    # ------------------------------------------------------------------
    best = Dict{Tuple{String,String}, Dict{String,Any}}()
    for entry in all_entries
        prover = canonical_prover(string(get(entry, "prover", "Unknown")))
        theorem = string(get(entry, "theorem", ""))
        key = (prover, theorem)
        if !haskey(best, key) || context_richness(entry) > context_richness(best[key])
            entry_copy = copy(entry)
            entry_copy["prover"] = prover
            best[key] = entry_copy
        end
    end

    deduped = collect(values(best))
    println("After deduplication: $(length(deduped)) unique (prover, theorem) pairs")
    println("Duplicates removed:  $(length(all_entries) - length(deduped))")

    # ------------------------------------------------------------------
    # 3. Assign fresh sequential IDs and sort by prover then theorem
    # ------------------------------------------------------------------
    sort!(deduped, by=e -> (get(e, "prover", ""), get(e, "theorem", "")))
    for (idx, entry) in enumerate(deduped)
        entry["id"] = idx
    end

    # ------------------------------------------------------------------
    # 4. Write unified JSONL
    # ------------------------------------------------------------------
    unified_path = joinpath(TRAINING_DIR, "proof_states_UNIFIED.jsonl")
    open(unified_path, "w") do fh
        for entry in deduped
            println(fh, JSON3.write(entry))
        end
    end
    println("\nWrote $(length(deduped)) proofs to $unified_path")

    # ------------------------------------------------------------------
    # 5. Compute statistics
    # ------------------------------------------------------------------
    prover_counts = Dict{String,Int}()
    source_counts = Dict{String,Int}()
    unique_theorems = Set{String}()
    vocab = Set{String}()

    for entry in deduped
        p = string(get(entry, "prover", "Unknown"))
        prover_counts[p] = get(prover_counts, p, 0) + 1
        s = string(get(entry, "source", "unknown"))
        source_counts[s] = get(source_counts, s, 0) + 1
        push!(unique_theorems, string(get(entry, "theorem", "")))
        # Vocabulary extraction
        goal_text = string(get(entry, "goal", ""))
        theorem_text = string(get(entry, "theorem", ""))
        union!(vocab, extract_words(goal_text))
        union!(vocab, extract_words(theorem_text))
    end

    provers_with_data = count(c -> c > 0, values(prover_counts))
    coverage_pct = round(provers_with_data / TOTAL_BACKENDS * 100; digits=1)

    # Sort prover_counts by descending count
    sorted_prover_counts = sort(collect(prover_counts); by=x -> -x[2])
    per_prover = Dict(k => v for (k, v) in sorted_prover_counts)

    # Top 50 sources
    sorted_sources = sort(collect(source_counts); by=x -> -x[2])
    per_source_top50 = Dict(k => v for (k, v) in sorted_sources[1:min(50, length(sorted_sources))])

    stats = Dict{String, Any}(
        "version" => "UNIFIED",
        "date" => string(today()),
        "total_proofs" => length(deduped),
        "unique_theorems" => length(unique_theorems),
        "provers_with_data" => provers_with_data,
        "total_backends" => TOTAL_BACKENDS,
        "coverage_percentage" => coverage_pct,
        "per_prover_counts" => per_prover,
        "per_source_counts_top50" => per_source_top50,
        "vocabulary_size" => length(vocab),
        "source_files_used" => file_counts,
    )

    stats_path = joinpath(TRAINING_DIR, "stats_UNIFIED.json")
    open(stats_path, "w") do fh
        write(fh, JSON3.write(stats))
    end
    println("Wrote statistics to $stats_path")

    # ------------------------------------------------------------------
    # 6. Write vocabulary file
    # ------------------------------------------------------------------
    vocab_path = joinpath(TRAINING_DIR, "vocabulary_UNIFIED.txt")
    open(vocab_path, "w") do fh
        for word in sort(collect(vocab))
            println(fh, word)
        end
    end
    println("Wrote $(length(vocab)) vocabulary words to $vocab_path")

    # ------------------------------------------------------------------
    # 7. Summary
    # ------------------------------------------------------------------
    println("\n" * "=" ^ 70)
    println("UNIFIED CORPUS SUMMARY")
    println("=" ^ 70)
    println("  Total proofs:        $(lpad(string(length(deduped)), 10))")
    println("  Unique theorems:     $(lpad(string(length(unique_theorems)), 10))")
    println("  Vocabulary words:    $(lpad(string(length(vocab)), 10))")
    println("  Provers with data:   $(lpad(string(provers_with_data), 10)) / $TOTAL_BACKENDS")
    println("  Coverage:            $(lpad(string(coverage_pct), 9))%")
    println()
    println("  Per-prover breakdown:")
    for (prover, count) in sorted_prover_counts
        println("    $(rpad(prover, 20)) $(lpad(string(count), 10))")
    end
    println("=" ^ 70)

    return 0
end

if abspath(PROGRAM_FILE) == @__FILE__
    exit(main())
end
