#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract proofs from mathlib3 (Lean 3) corpus and convert to ECHIDNA training
# format. Lean 3 is a sibling prover to Lean 4 — different syntax, different
# tactic language, different library. mathlib3 preserves a substantial body
# of formal mathematics that is not isomorphic to mathlib4; many specialty
# areas never ported.
#
# Corpus source: leanprover-community/mathlib (NOT mathlib4 — that has its
# own extractor). Expected vendor location: external_corpora/mathlib3/ —
# must be cloned before running this extractor.
#
# Key syntactic differences from mathlib4:
#   - Tactic blocks are `begin … end`, not `:= by …`
#   - mathlib3 uses lowercase module paths (`import data.nat.basic`), while
#     mathlib4 uses capitalised ones (`import Mathlib.Data.Nat.Basic`).
#   - mathlib3 has `universes u v` without `: Level` annotations.
#   - Namespaces close with `end <name>`; mathlib4 uses the same.
#
# Output format mirrors the mathlib4 extractor so the downstream ML layer
# sees a uniform schema across Lean 3 and Lean 4 corpora.

using JSON3

# Configuration
const MATHLIB3_DIR = "external_corpora/mathlib3"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_lean3.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_lean3.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_lean3.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_lean3.json")

# Start ID reserved for Lean 3 range — picked to avoid collisions with existing
# extractors. Widen if mathlib3 yields more than 500K proofs (unlikely).
const START_ID = 500_000

"""
    extract_lean3_proofs() -> Tuple{Vector, Vector, Vector}

Walk the mathlib3 tree, parse `theorem` / `lemma` / `def` blocks, extract the
proof statement and the tactic body, yield dictionaries matching the
ECHIDNA training-data schema. Safe on partial / missing vendoring —
returns empty vectors if MATHLIB3_DIR is absent.
"""
function extract_lean3_proofs()
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    current_id = START_ID

    # Widening (2026-04-18): walk mathlib3 plus additional Lean 3
    # community libraries (lean-liquid, flt-regular) to push toward
    # the 100K ML threshold.
    roots = String[]
    mathlib3_src = joinpath(MATHLIB3_DIR, "src")
    isdir(mathlib3_src) && push!(roots, mathlib3_src)
    for sibling in ("lean-liquid", "flt-regular")
        p = joinpath(dirname(MATHLIB3_DIR), sibling)
        isdir(p) && push!(roots, p)
    end
    if isempty(roots)
        println("mathlib3 source directory not found: $mathlib3_src")
        println("Clone with: git clone https://github.com/leanprover-community/mathlib " *
                "$MATHLIB3_DIR")
        return Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    end

    lean_files = String[]
    for root in roots
        for (rr, _dirs, files) in walkdir(root)
            for file in files
                if endswith(file, ".lean")
                    push!(lean_files, joinpath(rr, file))
                end
            end
        end
    end

    println("Found $(length(lean_files)) Lean 3 files across $(length(roots)) root(s)")

    # Lean 3 theorem-with-tactic-proof: `theorem NAME STATEMENT := begin … end`
    # Also matches `lemma`, `protected theorem`, etc. The `[^:]*?` eats the
    # statement up to the `:= begin` marker.
    begin_end_pattern = r"(?:protected\s+)?(theorem|lemma|def)\s+([a-zA-Z0-9_\.]+)\s+(.*?)\s*:=\s*begin\s+(.*?)\s+end"s
    # Term-mode proofs: `theorem NAME STATEMENT := term`. Stop before newline
    # or the next top-level declaration to avoid greediness.
    term_pattern = r"(?:protected\s+)?(theorem|lemma)\s+([a-zA-Z0-9_\.]+)\s+(.*?)\s*:=\s*([^\n].*?)(?=\n(?:theorem|lemma|def|namespace|end |@\[))"s

    # To keep first-run times reasonable, cap the file count. Remove cap once
    # full extraction is in the nightly job.
    cap = length(lean_files)  # no cap by default; override with env var if needed
    if haskey(ENV, "ECHIDNA_LEAN3_FILE_CAP")
        cap = parse(Int, ENV["ECHIDNA_LEAN3_FILE_CAP"])
    end

    for lean_file in first(lean_files, cap)
        try
            content = read(lean_file, String)

            # Tactic-mode proofs (begin … end).
            for m in eachmatch(begin_end_pattern, content)
                kind = strip(m.captures[1])
                name = strip(m.captures[2])
                statement = strip(m.captures[3])
                proof_body = strip(m.captures[4])

                if !isempty(name) && !isempty(statement)
                    push!(proof_states, Dict{String,Any}(
                        "id" => current_id,
                        "prover" => "Lean3",
                        "source_file" => relpath(lean_file, mathlib3_src),
                        "theorem" => name,
                        "kind" => kind,
                        "goal" => statement,
                        "context" => Any[],
                        "proof_mode" => "tactic",
                    ))

                    # Split tactic body on commas at brace depth 0. Rough
                    # heuristic — Lean 3 `begin … end` uses commas as tactic
                    # separators at the top level.
                    tactic_list = split_top_level_tactics(proof_body)
                    for (step, tactic) in enumerate(tactic_list)
                        if !isempty(strip(tactic))
                            push!(tactics, Dict{String,Any}(
                                "proof_id" => current_id,
                                "step" => step,
                                "tactic" => strip(tactic),
                                "prover" => "Lean3",
                            ))
                        end
                    end

                    current_id += 1
                end
            end

            # Term-mode proofs (:= term).
            for m in eachmatch(term_pattern, content)
                kind = strip(m.captures[1])
                name = strip(m.captures[2])
                statement = strip(m.captures[3])
                term = strip(m.captures[4])

                if !isempty(name) && !isempty(statement) && !isempty(term) &&
                   !startswith(term, "begin")
                    push!(proof_states, Dict{String,Any}(
                        "id" => current_id,
                        "prover" => "Lean3",
                        "source_file" => relpath(lean_file, mathlib3_src),
                        "theorem" => name,
                        "kind" => kind,
                        "goal" => statement,
                        "context" => Any[],
                        "proof_mode" => "term",
                    ))
                    current_id += 1
                end
            end

            # Premises: every import line is a premise edge.
            for line in eachline(IOBuffer(content))
                line = strip(line)
                if startswith(line, "import ")
                    mod = strip(replace(line, "import" => ""; count=1))
                    push!(premises, Dict{String,Any}(
                        "source_file" => relpath(lean_file, mathlib3_src),
                        "imports" => mod,
                        "prover" => "Lean3",
                    ))
                end
            end
        catch e
            println("Warning: error processing $lean_file: $e")
        end
    end

    return proof_states, tactics, premises
end

"""
    split_top_level_tactics(body::AbstractString) -> Vector{String}

Split a Lean 3 tactic block body on commas that appear at brace depth zero.
Ignores commas inside `{ … }`, `( … )`, `[ … ]`. Not perfect — Lean 3 allows
structured braces that change semantics — but good enough for first-pass
extraction.
"""
function split_top_level_tactics(body::AbstractString)
    out = String[]
    depth = 0
    buf = IOBuffer()
    for c in body
        if c in ('{', '(', '[')
            depth += 1
            print(buf, c)
        elseif c in ('}', ')', ']')
            depth -= 1
            print(buf, c)
        elseif c == ',' && depth == 0
            push!(out, String(take!(buf)))
        else
            print(buf, c)
        end
    end
    remaining = String(take!(buf))
    if !isempty(strip(remaining))
        push!(out, remaining)
    end
    return out
end

"""
    save_extracted_data(proof_states, tactics, premises)

Serialise the extracted records to JSONL + emit a stats summary.
"""
function save_extracted_data(proof_states::Vector, tactics::Vector, premises::Vector)
    mkpath(OUTPUT_DIR)

    open(PROOF_STATES_FILE, "w") do f
        for state in proof_states
            println(f, JSON3.write(state))
        end
    end

    open(TACTICS_FILE, "w") do f
        for tactic in tactics
            println(f, JSON3.write(tactic))
        end
    end

    open(PREMISES_FILE, "w") do f
        for premise in premises
            println(f, JSON3.write(premise))
        end
    end

    stats = Dict{String,Any}(
        "source" => "mathlib3",
        "prover" => "Lean3",
        "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(proof_states),
        "tactics_count" => length(tactics),
        "premises_count" => length(premises),
        "start_id" => START_ID,
        "end_id" => isempty(proof_states) ? START_ID : START_ID + length(proof_states) - 1,
    )

    open(STATS_FILE, "w") do f
        JSON3.pretty(f, stats)
    end

    println("Saved $(length(proof_states)) proof states to $PROOF_STATES_FILE")
    println("Saved $(length(tactics)) tactics to $TACTICS_FILE")
    println("Saved $(length(premises)) premises to $PREMISES_FILE")
    println("Saved statistics to $STATS_FILE")
end

using Dates

function main()
    println("ECHIDNA mathlib3 (Lean 3) Extraction")
    println("=" ^ 44)

    proof_states, tactics, premises = extract_lean3_proofs()

    if isempty(proof_states)
        println("No proofs extracted from mathlib3.")
        println("Vendor the source first: git clone " *
                "https://github.com/leanprover-community/mathlib " *
                "$MATHLIB3_DIR")
        return
    end

    save_extracted_data(proof_states, tactics, premises)
    println()
    println("Done. Next: rerun `just metrics` to pick up the new records and " *
            "retrain via scripts/retrain_from_verisim.jl.")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
