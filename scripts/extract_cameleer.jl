#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract proofs from Cameleer examples (OCaml with GOSPEL contracts).
# Vendor: https://github.com/ocaml-gospel/cameleer — examples/ directory.

using JSON3, Dates

const CAMELEER_DIR = "external_corpora/cameleer"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_cameleer.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_cameleer.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_cameleer.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_cameleer.json")
const START_ID = 800_000

function extract_cameleer_proofs()
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    current_id = START_ID

    examples = joinpath(CAMELEER_DIR, "examples")
    if !isdir(examples)
        println("Cameleer examples not found: $examples")
        println("Clone: git clone https://github.com/ocaml-gospel/cameleer $CAMELEER_DIR")
        return proof_states, tactics, premises
    end

    ml_files = String[]
    for (root, _, files) in walkdir(examples)
        for f in files
            endswith(f, ".ml") && push!(ml_files, joinpath(root, f))
        end
    end
    println("Found $(length(ml_files)) OCaml files with GOSPEL annotations")

    # GOSPEL comment: (*@ requires X *) or (*@ ensures Y *)
    # OCaml function with GOSPEL: let NAME ... = ... (*@ SPEC *)
    fn_pattern = r"let\s+([a-zA-Z0-9_']+)\s+([^=]*?)=\s*(.*?)\s*\(\*@\s*(.*?)\s*\*\)"s

    for f in ml_files
        try
            content = read(f, String)
            for m in eachmatch(fn_pattern, content)
                name = strip(m.captures[1])
                spec = strip(m.captures[4])
                if !isempty(name) && !isempty(spec)
                    push!(proof_states, Dict{String,Any}(
                        "id" => current_id,
                        "prover" => "Cameleer",
                        "source_file" => relpath(f, examples),
                        "theorem" => name,
                        "goal" => spec,
                        "context" => Any[],
                    ))
                    current_id += 1
                end
            end
        catch e
            println("Warning: $f: $e")
        end
    end
    return proof_states, tactics, premises
end

function save_extracted_data(ps, ts, pm)
    mkpath(OUTPUT_DIR)
    open(PROOF_STATES_FILE, "w") do f; for s in ps; println(f, JSON3.write(s)); end; end
    open(TACTICS_FILE, "w") do f; for t in ts; println(f, JSON3.write(t)); end; end
    open(PREMISES_FILE, "w") do f; for p in pm; println(f, JSON3.write(p)); end; end
    stats = Dict{String,Any}(
        "source" => "ocaml-gospel/cameleer examples",
        "prover" => "Cameleer", "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(ps), "tactics_count" => length(ts),
        "premises_count" => length(pm), "start_id" => START_ID,
        "end_id" => isempty(ps) ? START_ID : START_ID + length(ps) - 1)
    open(STATS_FILE, "w") do f; JSON3.pretty(f, stats); end
    println("Saved $(length(ps)) proof states")
end

function main()
    println("ECHIDNA Cameleer (OCaml/GOSPEL) Extraction"); println("=" ^ 44)
    ps, ts, pm = extract_cameleer_proofs()
    isempty(ps) ? println("No proofs extracted.") : save_extracted_data(ps, ts, pm)
end

if abspath(PROGRAM_FILE) == @__FILE__; main(); end
