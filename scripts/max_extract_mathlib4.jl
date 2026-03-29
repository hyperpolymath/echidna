#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# MAXIMUM mathlib4 Extraction - Extract ALL available Lean proofs.
# Comprehensive extraction from all .lean files.

using JSON3

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const MATHLIB4_DIR = "external_corpora/mathlib4"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_mathlib4_max.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_mathlib4_max.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_mathlib4_max.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_mathlib4_max.json")

# Start ID after CoqGym MAX (50000 + 10000 buffer = 60000)
const START_ID = 60000

"""
    extract_file_proofs(filepath::String, current_id::Int) -> Tuple

Extract all proofs from a single Lean file.
Returns (proof_states, tactics, premises, count).
"""
function extract_file_proofs(filepath::String, current_id::Int)
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    file_id = current_id

    try
        content = read(filepath, String)

        # Comprehensive Lean proof patterns
        patterns = [
            (r"theorem\s+([a-zA-Z0-9_'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\z))"s, "theorem"),
            (r"lemma\s+([a-zA-Z0-9_'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\z))"s, "lemma"),
            (r"proposition\s+([a-zA-Z0-9_'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\z))"s, "proposition"),
            (r"corollary\s+([a-zA-Z0-9_'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\z))"s, "corollary"),
            (r"example\s+([a-zA-Z0-9_'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\z))"s, "example"),
            (r"def\s+([a-zA-Z0-9_'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\z))"s, "definition"),
        ]

        for (pattern, proof_type) in patterns
            for m in eachmatch(pattern, content)
                try
                    name = strip(m.captures[1])
                    statement = strip(m.captures[2])

                    if !isempty(name) && !isempty(statement) && length(name) < 200
                        # Create proof state
                        proof_state = Dict{String,Any}(
                            "id" => file_id,
                            "prover" => "Lean",
                            "theorem" => name,
                            "goal" => statement[1:min(1000, length(statement))],
                            "context" => Any[],
                            "source" => "mathlib4",
                            "proof_type" => proof_type,
                        )
                        push!(proof_states, proof_state)

                        # Extract proof content
                        proof_start = m.offset + length(m.match)
                        remaining = content[min(proof_start, length(content)):end]

                        # Look for "by" clause or tactic blocks
                        by_match = match(r":=\s*by\s+([^\n]+)", remaining)
                        tactic_block_match = match(r":=\s*\n\s*([\s\S]*?)(?=\n\s*(?:@\[|\/--|\z))"s, remaining)

                        if by_match !== nothing
                            # Simple "by" clause
                            tactics_str = strip(by_match.captures[1])
                            individual_tactics = split(tactics_str, r"[\s,]+")

                            for (step, tactic) in enumerate(individual_tactics)
                                tactic_str = String(tactic)
                                if !isempty(tactic_str) && length(tactic_str) < 100
                                    push!(tactics, Dict{String,Any}(
                                        "proof_id" => file_id,
                                        "step" => step,
                                        "tactic" => tactic_str,
                                        "prover" => "Lean",
                                        "tactic_type" => "by_clause",
                                    ))
                                end
                            end
                        elseif tactic_block_match !== nothing
                            # Multi-line tactic block
                            tactic_content = tactic_block_match.captures[1]

                            # Extract individual tactics
                            tactic_lines = [strip(line) for line in split(tactic_content, '\n') if !isempty(strip(line))]

                            for (step, tactic_line) in enumerate(tactic_lines)
                                if !startswith(tactic_line, "--")
                                    # Remove comments
                                    tactic = strip(replace(tactic_line, r"--.*$" => ""))
                                    if !isempty(tactic) && length(tactic) < 200
                                        push!(tactics, Dict{String,Any}(
                                            "proof_id" => file_id,
                                            "step" => step,
                                            "tactic" => String(tactic),
                                            "prover" => "Lean",
                                            "tactic_type" => "tactic_block",
                                        ))
                                    end
                                end
                            end
                        end

                        # Extract premises/hypotheses
                        hyp_patterns = [
                            r"intro\s+([a-zA-Z0-9_\s]+)",
                            r"\u27e8([a-zA-Z0-9_\s,]+)\u27e9",  # angle brackets
                            r"let\s+([a-zA-Z0-9_]+)\s*:=",
                            r"have\s+([a-zA-Z0-9_]+)\s*:=",
                        ]

                        for hyp_pattern in hyp_patterns
                            for hyp_match in eachmatch(Regex(hyp_pattern), remaining)
                                hyps = [strip(h) for h in split(hyp_match.captures[1], ',')]
                                for hyp in hyps
                                    if !isempty(hyp) && length(hyp) < 50
                                        push!(premises, Dict{String,Any}(
                                            "proof_id" => file_id,
                                            "premise" => String(hyp),
                                            "prover" => "Lean",
                                            "theorem" => name,
                                            "source" => "mathlib4",
                                        ))
                                    end
                                end
                            end
                        end

                        file_id += 1
                    end
                catch
                    continue
                end
            end
        end

        return proof_states, tactics, premises, file_id - current_id

    catch e
        println("  WARNING: Error processing $filepath: $e")
        return Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[], 0
    end
end

"""
    save_extracted_data(proof_states, tactics, premises, next_id, lean_files_count)

Save extracted data with progress tracking. Uses atomic rename for safety.
"""
function save_extracted_data(proof_states, tactics, premises, next_id; lean_files_count::Int=0)
    mkpath(OUTPUT_DIR)

    temp_states = PROOF_STATES_FILE * ".tmp"
    temp_tactics = TACTICS_FILE * ".tmp"
    temp_premises = PREMISES_FILE * ".tmp"

    try
        open(temp_states, "w") do f
            for state in proof_states
                println(f, JSON3.write(state))
            end
        end

        open(temp_tactics, "w") do f
            for tactic in tactics
                println(f, JSON3.write(tactic))
            end
        end

        open(temp_premises, "w") do f
            for premise in premises
                println(f, JSON3.write(premise))
            end
        end

        # Atomic rename
        for (temp_file, final_file) in [(temp_states, PROOF_STATES_FILE),
                                         (temp_tactics, TACTICS_FILE),
                                         (temp_premises, PREMISES_FILE)]
            isfile(final_file) && rm(final_file)
            mv(temp_file, final_file)
        end

        # Save statistics
        stats = Dict{String,Any}(
            "source" => "mathlib4_MAX",
            "extraction_date" => "2026-03-20",
            "proof_states_count" => length(proof_states),
            "tactics_count" => length(tactics),
            "premises_count" => length(premises),
            "start_id" => START_ID,
            "end_id" => next_id - 1,
            "files_processed" => lean_files_count,
            "extraction_method" => "comprehensive_regex",
        )

        open(STATS_FILE, "w") do f
            write(f, JSON3.write(stats))
        end

        println("  Saved progress: $(length(proof_states)) proofs, $(length(tactics)) tactics, $(length(premises)) premises")

    catch e
        println("  ERROR saving data: $e")
        for temp_file in [temp_states, temp_tactics, temp_premises]
            isfile(temp_file) && rm(temp_file)
        end
    end
end

"""
    max_extract_mathlib4()

Maximum extraction from all mathlib4 files.
"""
function max_extract_mathlib4()
    println("MAXIMUM mathlib4 Extraction")
    println("=" ^ 50)

    # Find ALL .lean files
    mathlib4_proofs_dir = joinpath(MATHLIB4_DIR, "Mathlib")

    if !isdir(mathlib4_proofs_dir)
        println("ERROR: mathlib4 directory not found: $mathlib4_proofs_dir")
        return
    end

    # Get all .lean files
    lean_files = String[]
    for (root, _dirs, files) in walkdir(mathlib4_proofs_dir)
        for file in files
            if endswith(file, ".lean")
                push!(lean_files, joinpath(root, file))
            end
        end
    end

    println("Found $(length(lean_files)) Lean files to process")

    # Process files in batches
    all_proof_states = Dict{String,Any}[]
    all_tactics = Dict{String,Any}[]
    all_premises = Dict{String,Any}[]
    current_id = START_ID
    batch_size = 50

    for i in 1:batch_size:length(lean_files)
        batch = lean_files[i:min(i + batch_size - 1, length(lean_files))]
        batch_num = div(i - 1, batch_size) + 1
        total_batches = div(length(lean_files) - 1, batch_size) + 1
        println("Processing batch $batch_num/$total_batches ($(length(batch)) files)...")

        batch_results = Tuple{String,Int}[]
        for filepath in batch
            try
                proofs, tacs, prems, count = extract_file_proofs(filepath, current_id)
                if count > 0
                    append!(all_proof_states, proofs)
                    append!(all_tactics, tacs)
                    append!(all_premises, prems)
                    current_id += count
                    push!(batch_results, (filepath, count))
                end
            catch e
                println("  ERROR in $filepath: $e")
            end
        end

        # Show batch progress
        successful = count(r -> r[2] > 0, batch_results)
        total_count = sum(r[2] for r in batch_results; init=0)
        println("  Batch complete: $successful/$(length(batch)) files, $total_count proofs extracted")

        # Save progress periodically
        if length(all_proof_states) >= 500
            save_extracted_data(all_proof_states, all_tactics, all_premises, current_id; lean_files_count=length(lean_files))
            println("  Checkpoint saved: $(length(all_proof_states)) proofs so far")
        end
    end

    # Final save
    save_extracted_data(all_proof_states, all_tactics, all_premises, current_id; lean_files_count=length(lean_files))

    println("\nMAXIMUM mathlib4 Extraction Complete!")
    println("   Total Proofs: $(length(all_proof_states))")
    println("   Total Tactics: $(length(all_tactics))")
    println("   Total Premises: $(length(all_premises))")
    println("   ID Range: $START_ID - $(current_id - 1)")
end

if abspath(PROGRAM_FILE) == @__FILE__
    max_extract_mathlib4()
end
