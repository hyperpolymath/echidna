#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract proofs from the Abella examples corpus. Abella is the canonical
# classical prover for nominal logic / HOAS / λ-tree syntax — the first
# prover in ECHIDNA's roster to cover the binder-management family
# (TypeDiscipline::Nominal).
#
# Corpus source: abella-prover/abella (examples/ directory). Small by
# mainstream-prover standards (~200–400 theorems depending on which
# branches are vendored) but qualitatively distinct: proofs of object-
# language metatheorems using ∇-quantifier-based reasoning, not
# expressible in the way other provers reason. High marginal value for
# the CANON vocabulary and for the Phase 5 Arbiter's cross-discipline
# analogy detection.
#
# Expected vendor location: external_corpora/abella/examples/

using JSON3
using Dates

const ABELLA_DIR = "external_corpora/abella"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_abella.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_abella.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_abella.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_abella.json")

# ID range reserved for Abella. Chosen high so it never collides even
# if mathlib3 extraction grows to ~500K proofs.
const START_ID = 600_000

"""
    extract_abella_proofs() -> Tuple{Vector, Vector, Vector}

Walk `external_corpora/abella/examples/`, parse `.thm` files, extract
`Theorem <name> : <statement>` declarations and their proof scripts.
"""
function extract_abella_proofs()
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    current_id = START_ID

    examples_dir = joinpath(ABELLA_DIR, "examples")

    if !isdir(examples_dir)
        println("Abella examples directory not found: $examples_dir")
        println("Clone with: git clone https://github.com/abella-prover/abella $ABELLA_DIR")
        return Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    end

    thm_files = String[]
    for (root, _dirs, files) in walkdir(examples_dir)
        for file in files
            if endswith(file, ".thm")
                push!(thm_files, joinpath(root, file))
            end
        end
    end

    println("Found $(length(thm_files)) Abella .thm files")

    # Abella theorem: "Theorem <name> : <statement>." followed by a
    # sequence of tactic lines ending at "." (or multiline tactics
    # ending in "." on their own line). Proof terminates at "Proof
    # completed." but the source doesn't contain that line —
    # termination is detected by the next top-level declaration.
    theorem_pattern = r"Theorem\s+([a-zA-Z0-9_']+)\s*:\s*(.*?)\.\s*\n(.*?)(?=\n(?:Theorem|Define|Kind|Type|Specification|CoDefine|Close|Split|Query|%)|$)"s

    # Widening (2026-04-18): also harvest Define / CoDefine / Kind /
    # Type / Query / Split declarations. Each is a named object that
    # carries structural signal for ML. Split and Query are proof
    # commands that refer to existing theorems (follow-up proofs).
    define_pattern = r"(Co)?Define\s+([a-zA-Z0-9_']+)\s*:\s*(.*?)\s*by\b"s
    kind_pattern = r"Kind\s+([a-zA-Z0-9_']+)\s+(.*?)\."s
    type_pattern = r"Type\s+([a-zA-Z0-9_']+)\s+(.*?)\."s
    query_pattern = r"Query\s+(.+?)\."s
    split_pattern = r"Split\s+([a-zA-Z0-9_']+)\s+as\s+([^.]+)\."s

    # Specification imports (λProlog signatures).
    spec_pattern = r"Specification\s+\"([^\"]+)\""

    for thm_file in thm_files
        content = try
            read(thm_file, String)
        catch
            continue
        end
        rel = relpath(thm_file, examples_dir)

        for spec_m in eachmatch(spec_pattern, content)
            push!(premises, Dict{String,Any}(
                "source_file" => rel,
                "specification" => spec_m.captures[1],
                "prover" => "Abella",
            ))
        end

        # Theorems (primary extraction path, unchanged).
        matches = try collect(eachmatch(theorem_pattern, content)) catch; Any[] end
        for m in matches
            name = strip(m.captures[1])
            statement = strip(m.captures[2])
            proof_body = strip(m.captures[3])
            (isempty(name) || isempty(statement)) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Abella",
                "discipline" => "Nominal",
                "source_file" => rel,
                "theorem" => name,
                "goal" => first(statement, 2000),
                "context" => Any[],
                "proof_mode" => "interactive",
            ))
            tactic_list = split_abella_tactics(proof_body)
            for (step, tactic) in enumerate(tactic_list)
                isempty(strip(tactic)) && continue
                push!(tactics, Dict{String,Any}(
                    "proof_id" => current_id, "step" => step,
                    "tactic" => strip(tactic),
                    "prover" => "Abella", "discipline" => "Nominal",
                ))
            end
            current_id += 1
        end

        matches = try collect(eachmatch(define_pattern, content)) catch; Any[] end
        for m in matches
            cokind = m.captures[1] === nothing ? "Define" : "CoDefine"
            name = strip(m.captures[2])
            body = first(strip(m.captures[3]), 2000)
            (isempty(name) || isempty(body)) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Abella",
                "discipline" => "Nominal",
                "source_file" => rel,
                "theorem" => name,
                "goal" => body,
                "kind" => cokind,
                "context" => Any[],
            ))
            current_id += 1
        end

        for (pat, kind) in ((kind_pattern, "Kind"),
                            (type_pattern, "Type"))
            matches = try collect(eachmatch(pat, content)) catch; Any[] end
            for m in matches
                name = strip(m.captures[1])
                body = first(strip(m.captures[2]), 1000)
                isempty(name) && continue
                push!(proof_states, Dict{String,Any}(
                    "id" => current_id, "prover" => "Abella",
                    "discipline" => "Nominal",
                    "source_file" => rel,
                    "theorem" => name,
                    "goal" => body,
                    "kind" => kind,
                    "context" => Any[],
                ))
                current_id += 1
            end
        end

        matches = try collect(eachmatch(query_pattern, content)) catch; Any[] end
        for (i, m) in enumerate(matches)
            body = first(strip(m.captures[1]), 1000)
            isempty(body) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Abella",
                "discipline" => "Nominal",
                "source_file" => rel,
                "theorem" => "query_$(i)",
                "goal" => body,
                "kind" => "Query",
                "context" => Any[],
            ))
            current_id += 1
        end

        matches = try collect(eachmatch(split_pattern, content)) catch; Any[] end
        for m in matches
            base = strip(m.captures[1])
            branches = first(strip(m.captures[2]), 400)
            isempty(base) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Abella",
                "discipline" => "Nominal",
                "source_file" => rel,
                "theorem" => "$(base)_split",
                "goal" => branches,
                "kind" => "Split",
                "context" => Any[],
            ))
            current_id += 1
        end
    end

    return proof_states, tactics, premises
end

"""
    split_abella_tactics(body) -> Vector{String}

Abella tactics are period-separated. Simple split on `.` at the end of
a line, with a small guard for common multi-line tactic forms
(`induction on X.`, `case H.`, `apply H to ...`).
"""
function split_abella_tactics(body::AbstractString)
    out = String[]
    for line in eachline(IOBuffer(body))
        line = strip(line)
        isempty(line) && continue
        startswith(line, "%") && continue  # Abella comments
        if endswith(line, ".")
            push!(out, String(rstrip(line, '.')))
        else
            push!(out, String(line))
        end
    end
    return out
end

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
        "source" => "abella-prover/abella examples",
        "prover" => "Abella",
        "discipline" => "Nominal",
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

function main()
    println("ECHIDNA Abella (Nominal logic / HOAS) Extraction")
    println("=" ^ 48)

    proof_states, tactics, premises = extract_abella_proofs()

    if isempty(proof_states)
        println("No proofs extracted from Abella.")
        println("Vendor the source first: git clone " *
                "https://github.com/abella-prover/abella $ABELLA_DIR")
        return
    end

    save_extracted_data(proof_states, tactics, premises)
    println()
    println("Done. Next: rerun `just metrics` to pick up the new records.")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
