#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract proofs from ACL2s examples.
# Vendor: https://github.com/acl2s/acl2s (Northeastern's ACL2 Sedan).

using JSON3, Dates

const ACL2S_DIR = "external_corpora/acl2s"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_acl2s.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_acl2s.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_acl2s.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_acl2s.json")
const START_ID = 900_000

function extract_acl2s_proofs()
    proof_states = Dict{String,Any}[]; tactics = Dict{String,Any}[]; premises = Dict{String,Any}[]
    current_id = START_ID
    if !isdir(ACL2S_DIR)
        println("ACL2s directory not found: $ACL2S_DIR")
        println("Clone: git clone https://github.com/acl2s/acl2s $ACL2S_DIR")
        return proof_states, tactics, premises
    end

    lisp_files = String[]
    for (root, _, files) in walkdir(ACL2S_DIR)
        for f in files
            (endswith(f, ".lisp") || endswith(f, ".acl2")) && push!(lisp_files, joinpath(root, f))
        end
    end
    println("Found $(length(lisp_files)) ACL2s source files")

    # ACL2s: (defthm NAME STATEMENT :hints …) or (defun NAME …)
    defthm_pattern = r"\(defthm\s+([a-zA-Z0-9_\-]+)\s+(.+?)(?=\s*:hints|\s*\)\s*(?:\n|\Z))"s

    for f in lisp_files
        try
            content = read(f, String)
            for m in eachmatch(defthm_pattern, content)
                name = strip(m.captures[1])
                statement = strip(m.captures[2])
                if !isempty(name) && !isempty(statement)
                    push!(proof_states, Dict{String,Any}(
                        "id" => current_id, "prover" => "ACL2s",
                        "source_file" => relpath(f, ACL2S_DIR),
                        "theorem" => name, "goal" => statement,
                        "context" => Any[],
                    ))
                    # Emit premises: ACL2s identifiers from theorem statement
                    for hm in eachmatch(r"\b([a-zA-Z][a-zA-Z0-9_\-]{1,40})\b", statement)
                        h = strip(hm.captures[1])
                        !isempty(h) && length(h) < 50 && push!(premises, Dict{String,Any}(
                            "proof_id"=>current_id, "premise"=>h,
                            "prover"=>"ACL2s", "theorem"=>name, "source"=>"acl2s"))
                    end
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
        "source" => "acl2s/acl2s", "prover" => "ACL2s",
        "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(ps), "tactics_count" => length(ts),
        "premises_count" => length(pm), "start_id" => START_ID,
        "end_id" => isempty(ps) ? START_ID : START_ID + length(ps) - 1)
    open(STATS_FILE, "w") do f; JSON3.pretty(f, stats); end
    println("Saved $(length(ps)) proof states")
end

function main()
    println("ECHIDNA ACL2s Extraction"); println("=" ^ 24)
    ps, ts, pm = extract_acl2s_proofs()
    isempty(ps) ? println("No proofs extracted.") : save_extracted_data(ps, ts, pm)
end

if abspath(PROGRAM_FILE) == @__FILE__; main(); end
