#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract proofs from Isabelle/ZF (Zermelo-Fraenkel set-theory object logic).
# Distinct from Isabelle/HOL (which has its own extractor via AFP).
# Vendor: Isabelle distribution's `src/ZF/` directory + the ZF-flavoured AFP
# entries. Both ship in the standard Isabelle download.

using JSON3, Dates

const ISABELLE_ZF_DIR = "external_corpora/isabelle/src/ZF"
const AFP_ZF_DIR = "external_corpora/afp_zf" # ZF-flavoured AFP entries
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_isabelle_zf.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_isabelle_zf.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_isabelle_zf.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_isabelle_zf.json")
const START_ID = 1_000_000

function extract_isabelle_zf_proofs()
    proof_states = Dict{String,Any}[]; tactics = Dict{String,Any}[]; premises = Dict{String,Any}[]
    current_id = START_ID

    thy_files = String[]
    for dir in [ISABELLE_ZF_DIR, AFP_ZF_DIR]
        if isdir(dir)
            for (root, _, files) in walkdir(dir)
                for f in files
                    endswith(f, ".thy") && push!(thy_files, joinpath(root, f))
                end
            end
        end
    end
    if isempty(thy_files)
        println("No Isabelle/ZF theory files found.")
        println("Vendor: copy Isabelle's src/ZF/ into $ISABELLE_ZF_DIR")
        return proof_states, tactics, premises
    end
    println("Found $(length(thy_files)) Isabelle/ZF .thy files")

    # Isabelle/Isar: theorem NAME: "STATEMENT" <proof>
    theorem_pattern = r"(?:theorem|lemma|corollary)\s+([a-zA-Z0-9_.']+)\s*:\s*\"(.*?)\"\s*(?:proof|apply|by|done|sorry)"s

    for f in thy_files
        try
            content = read(f, String)
            for m in eachmatch(theorem_pattern, content)
                name = strip(m.captures[1])
                statement = strip(m.captures[2])
                if !isempty(name) && !isempty(statement)
                    push!(proof_states, Dict{String,Any}(
                        "id" => current_id, "prover" => "IsabelleZF",
                        "logic" => "ZF",
                        "source_file" => f,
                        "theorem" => name, "goal" => statement,
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
        "source" => "Isabelle src/ZF + AFP/ZF", "prover" => "IsabelleZF",
        "logic" => "ZF", "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(ps), "tactics_count" => length(ts),
        "premises_count" => length(pm), "start_id" => START_ID,
        "end_id" => isempty(ps) ? START_ID : START_ID + length(ps) - 1)
    open(STATS_FILE, "w") do f; JSON3.pretty(f, stats); end
    println("Saved $(length(ps)) proof states")
end

function main()
    println("ECHIDNA Isabelle/ZF Extraction"); println("=" ^ 30)
    ps, ts, pm = extract_isabelle_zf_proofs()
    isempty(ps) ? println("No proofs extracted.") : save_extracted_data(ps, ts, pm)
end

if abspath(PROGRAM_FILE) == @__FILE__; main(); end
