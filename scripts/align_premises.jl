#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# align_premises.jl — rebuild training_data/premises_COMPLETE.jsonl with proof_ids
# that match the fresh sequential ids written by merge_corpus.jl into
# training_data/proof_states_UNIFIED.jsonl.
#
# Background
# ----------
# The per-prover extractors (scripts/extract_*.jl and scripts/max_extract_*.jl)
# emit proof_states and premises sharing a per-extractor-local integer id space:
#
#     {"id": 60123, "prover": "Lean", "theorem": "Foo.bar", ...}     (proof_state)
#     {"proof_id": 60123, "prover": "Lean", "theorem": "Foo.bar", ...} (premise)
#
# scripts/merge_corpus.jl then writes proof_states_UNIFIED.jsonl after dedup
# by (prover, theorem) and **rewrites every proof_state's id to a fresh
# sequential counter (1..N)**.  The premise files retain the original
# extractor ids, so proof_state.id and premise.proof_id no longer share an id
# space — the dataloader's join by proof_id matches ~0% of records.
#
# This script rebuilds premises_COMPLETE.jsonl using the
# (canonical_prover, theorem) pair as the durable join key (which merge_corpus
# already guarantees is unique within UNIFIED).  For every premise record,
# we look up the fresh id assigned by merge_corpus and rewrite
# `proof_id := UNIFIED_id`.  Records whose (prover, theorem) does not appear
# in UNIFIED are dropped and counted.
#
# Usage
# -----
#   julia --project=src/julia scripts/align_premises.jl
#
# Outputs
# -------
#   training_data/premises_COMPLETE.jsonl          — aligned premises
#   training_data/premises_ALIGNED_stats.json      — coverage report
#
# Run this after merge_corpus.jl and before run_training.jl.

using JSON3

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

const REPO_ROOT   = dirname(dirname(abspath(@__FILE__)))
const TRAINING_DIR = joinpath(REPO_ROOT, "training_data")

const UNIFIED_PATH = joinpath(TRAINING_DIR, "proof_states_UNIFIED.jsonl")
const OUT_PATH     = joinpath(TRAINING_DIR, "premises_COMPLETE.jsonl")
const STATS_PATH   = joinpath(TRAINING_DIR, "premises_ALIGNED_stats.json")

# Every premises_*.jsonl in training_data/ is a candidate source, except the
# output file itself and any ALIGNED_stats JSON we emit.  We also skip the
# timestamped `premises_<YYYY-MM-DD>.jsonl` snapshots by default but include
# them when ECHIDNA_ALIGN_INCLUDE_DATED=1.
function collect_premise_sources()
    sources = String[]
    for f in readdir(TRAINING_DIR; join=true)
        base = basename(f)
        startswith(base, "premises_")     || continue
        endswith(base, ".jsonl")          || continue
        base == "premises_COMPLETE.jsonl" && continue
        if get(ENV, "ECHIDNA_ALIGN_INCLUDE_DATED", "0") != "1" &&
           occursin(r"^premises_\d{4}-\d{2}-\d{2}\.jsonl$", base)
            continue
        end
        push!(sources, f)
    end
    sort!(sources)
    return sources
end

# ---------------------------------------------------------------------------
# Prover-name canonicalisation — must match merge_corpus.jl's mapping.
# Keep this in lockstep with scripts/merge_corpus.jl's PROVER_CANONICAL.
# ---------------------------------------------------------------------------

const PROVER_CANONICAL = Dict(
    "Lean4"      => "Lean",
    "Rocq"       => "Coq",
    "Fstar"      => "F*",
    "CVC4"       => "CVC5",
    "AltErgo"    => "Alt-Ergo",
    "HOL Light"  => "HOLLight",
    "E Prover"   => "EProver",
    "OR-Tools"   => "ORTools",
)

canon(prover::AbstractString) = get(PROVER_CANONICAL, String(prover), String(prover))

# ---------------------------------------------------------------------------
# Build the (canonical_prover, theorem) → fresh_id index from UNIFIED.
# ---------------------------------------------------------------------------

function build_unified_index(path::String)
    isfile(path) || error("missing $(path); run scripts/merge_corpus.jl first.")
    index = Dict{Tuple{String,String},Int}()
    open(path, "r") do fh
        for line in eachline(fh)
            isempty(strip(line)) && continue
            entry = try
                JSON3.read(line, Dict{String,Any})
            catch
                continue
            end
            prover  = canon(get(entry, "prover", ""))
            theorem = String(get(entry, "theorem", ""))
            new_id  = get(entry, "id", nothing)
            (isempty(prover) || isempty(theorem) || new_id === nothing) && continue
            key = (prover, theorem)
            # First-write wins.  merge_corpus already dedupes by (prover,theorem)
            # so collisions here would indicate a merge bug — report and keep
            # the earlier id.
            if haskey(index, key) && index[key] != new_id
                @warn "duplicate (prover,theorem) in UNIFIED" prover=prover theorem=theorem first=index[key] second=new_id
                continue
            end
            index[key] = Int(new_id)
        end
    end
    return index
end

# ---------------------------------------------------------------------------
# Walk every premise source, rewrite proof_id, and emit premises_COMPLETE.
# ---------------------------------------------------------------------------

function align_premises(index::Dict{Tuple{String,String},Int}, sources::Vector{String})
    written = 0
    dropped_no_theorem   = 0
    dropped_no_match     = 0
    dropped_malformed    = 0
    per_source           = Dict{String,Dict{String,Int}}()

    open(OUT_PATH, "w") do out
        for src in sources
            s_written = 0
            s_dropped = 0
            open(src, "r") do fh
                for line in eachline(fh)
                    isempty(strip(line)) && continue
                    rec = try
                        JSON3.read(line, Dict{String,Any})
                    catch
                        dropped_malformed += 1
                        s_dropped += 1
                        continue
                    end
                    prover  = canon(get(rec, "prover", ""))
                    theorem = String(get(rec, "theorem", ""))
                    if isempty(prover) || isempty(theorem)
                        dropped_no_theorem += 1
                        s_dropped += 1
                        continue
                    end
                    new_id = get(index, (prover, theorem), nothing)
                    if new_id === nothing
                        dropped_no_match += 1
                        s_dropped += 1
                        continue
                    end
                    rec["proof_id"] = new_id
                    println(out, JSON3.write(rec))
                    written += 1
                    s_written += 1
                end
            end
            per_source[basename(src)] = Dict(
                "written" => s_written,
                "dropped" => s_dropped,
            )
        end
    end

    return (
        written               = written,
        dropped_no_theorem    = dropped_no_theorem,
        dropped_no_match      = dropped_no_match,
        dropped_malformed     = dropped_malformed,
        per_source            = per_source,
    )
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function main()
    println("align_premises — reconcile premise proof_ids with proof_states_UNIFIED")
    println("=" ^ 72)

    println("\nBuilding (prover, theorem) → fresh_id index from UNIFIED...")
    index = build_unified_index(UNIFIED_PATH)
    println("  $(length(index)) (prover, theorem) pairs loaded.")

    sources = collect_premise_sources()
    println("\nPremise sources ($(length(sources)) files):")
    for s in sources
        println("  $(basename(s))")
    end

    println("\nAligning...")
    result = align_premises(index, sources)

    total_in = result.written + result.dropped_no_theorem +
               result.dropped_no_match + result.dropped_malformed
    match_rate = total_in == 0 ? 0.0 : 100.0 * result.written / total_in

    println("\nResults")
    println("-" ^ 72)
    println("  Wrote            : $(result.written) records to $(OUT_PATH)")
    println("  Dropped (no key) : $(result.dropped_no_theorem) (missing prover or theorem)")
    println("  Dropped (no match): $(result.dropped_no_match) (theorem not in UNIFIED)")
    println("  Dropped (bad json): $(result.dropped_malformed)")
    println("  Match rate       : $(round(match_rate; digits=2))%")

    println("\nPer source:")
    for (name, counts) in sort(collect(result.per_source); by = p -> p[1])
        println("  $(rpad(name, 40)) written=$(counts["written"])  dropped=$(counts["dropped"])")
    end

    # Persist a machine-readable stats file alongside the output.
    stats = Dict(
        "unified_path"          => UNIFIED_PATH,
        "output_path"           => OUT_PATH,
        "unified_index_size"    => length(index),
        "sources"               => [basename(s) for s in sources],
        "written"               => result.written,
        "dropped_no_theorem"    => result.dropped_no_theorem,
        "dropped_no_match"      => result.dropped_no_match,
        "dropped_malformed"     => result.dropped_malformed,
        "match_rate_percent"    => match_rate,
        "per_source"            => result.per_source,
    )
    open(STATS_PATH, "w") do fh
        JSON3.pretty(fh, stats)
    end
    println("\nStats written to $(STATS_PATH)")

    if result.written == 0
        println("\nERROR: 0 records written.  Check that the premise files carry 'prover' and 'theorem' fields.")
        exit(2)
    end
    return 0
end

main()
