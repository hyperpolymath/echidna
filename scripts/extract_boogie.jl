#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract verification conditions from Boogie .bpl files.
# Vendor: https://github.com/boogie-org/boogie Test/ directory + any
# Dafny-generated .bpl dumps, any VCC / Chalice test suites.

using JSON3, Dates

const BOOGIE_DIR = "external_corpora/boogie"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_boogie.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_boogie.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_boogie.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_boogie.json")
const START_ID = 1_100_000

function extract_boogie_programs()
    proof_states = Dict{String,Any}[]; tactics = Dict{String,Any}[]; premises = Dict{String,Any}[]
    current_id = START_ID

    if !isdir(BOOGIE_DIR)
        println("Boogie corpus not found: $BOOGIE_DIR")
        println("Clone: git clone https://github.com/boogie-org/boogie $BOOGIE_DIR")
        return proof_states, tactics, premises
    end

    bpl_files = String[]
    for (root, _, files) in walkdir(BOOGIE_DIR)
        for f in files
            endswith(f, ".bpl") && push!(bpl_files, joinpath(root, f))
        end
    end
    println("Found $(length(bpl_files)) Boogie .bpl files")

    # Boogie: procedure NAME(args) returns(...) { … }; requires / ensures
    proc_pattern = r"procedure\s+([a-zA-Z0-9_]+)\s*\([^)]*\)\s*(?:returns\s*\([^)]*\))?\s*(.*?)(?:\{|;)"s

    for f in bpl_files
        try
            content = read(f, String)
            for m in eachmatch(proc_pattern, content)
                name = strip(m.captures[1])
                contract = strip(m.captures[2])
                if !isempty(name)
                    push!(proof_states, Dict{String,Any}(
                        "id" => current_id, "prover" => "Boogie",
                        "source_file" => relpath(f, BOOGIE_DIR),
                        "theorem" => name, "goal" => contract,
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
        "source" => "boogie-org/boogie Test/", "prover" => "Boogie",
        "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(ps), "tactics_count" => length(ts),
        "premises_count" => length(pm), "start_id" => START_ID,
        "end_id" => isempty(ps) ? START_ID : START_ID + length(ps) - 1)
    open(STATS_FILE, "w") do f; JSON3.pretty(f, stats); end
    println("Saved $(length(ps)) proof states")
end

function main()
    println("ECHIDNA Boogie (intermediate verification language) Extraction")
    println("=" ^ 60)
    ps, ts, pm = extract_boogie_programs()
    isempty(ps) ? println("No programs extracted.") : save_extracted_data(ps, ts, pm)
end

if abspath(PROGRAM_FILE) == @__FILE__; main(); end
