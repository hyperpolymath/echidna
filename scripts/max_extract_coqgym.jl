#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# MAXIMUM CoqGym Extraction - Extract ALL available proofs.
# Uses comprehensive regex patterns and processes ALL .v files.

using JSON3

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const COQGYM_DIR = "external_corpora/CoqGym"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_coqgym_max.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_coqgym_max.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_coqgym_max.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_coqgym_max.json")

# Start ID after current max (47742 + buffer)
const START_ID = 50000

"""
    extract_file_proofs(filepath::String) -> Tuple

Extract all proofs from a single Coq file.
Returns (proof_states, tactics, premises, count).
"""
function extract_file_proofs(filepath::String)
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    file_id = START_ID  # Will be adjusted by caller

    try
        content = read(filepath, String)

        # Comprehensive theorem/lemma patterns
        patterns = [
            (r"Theorem\s+([a-zA-Z0-9_'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\z))"s, "theorem"),
            (r"Lemma\s+([a-zA-Z0-9_'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\z))"s, "lemma"),
            (r"Proposition\s+([a-zA-Z0-9_'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\z))"s, "proposition"),
            (r"Corollary\s+([a-zA-Z0-9_'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\z))"s, "corollary"),
            (r"Fact\s+([a-zA-Z0-9_'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\z))"s, "fact"),
            (r"Remark\s+([a-zA-Z0-9_'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\z))"s, "remark"),
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
                            "prover" => "Coq",
                            "theorem" => name,
                            "goal" => statement[1:min(1000, length(statement))],
                            "context" => Any[],
                            "source" => "CoqGym",
                            "proof_type" => proof_type,
                        )
                        push!(proof_states, proof_state)

                        # Extract proof content (if available)
                        proof_start = m.offset + length(m.match)
                        remaining = content[min(proof_start, length(content)):end]
                        proof_match = match(r"Proof\.(.*?)(?=\n\s*(?:Qed|Defined|Save)\.)"s, remaining)

                        if proof_match !== nothing
                            proof_content = proof_match.captures[1]

                            # Extract tactics - comprehensive patterns
                            tactic_patterns = [
                                (r"\.\s*([a-zA-Z0-9_]+)", "simple"),
                                (r"apply\s+([a-zA-Z0-9_\.]+)", "apply"),
                                (r"intros?\s+([a-zA-Z0-9_\s]+)", "intros"),
                                (r"rewrite\s+([^\n]+)", "rewrite"),
                                (r"set\s+\(([^)]+)\)", "set"),
                                (r"pose\s+([^\n]+)", "pose"),
                                (r"assert\s+\(([^)]+)\)", "assert"),
                            ]

                            for (step, (tactic_pattern, tactic_type)) in enumerate(tactic_patterns)
                                for tactic_match in eachmatch(Regex(tactic_pattern), proof_content)
                                    tactic = strip(tactic_match.captures[1])
                                    if !isempty(tactic) && length(tactic) < 100
                                        push!(tactics, Dict{String,Any}(
                                            "proof_id" => file_id,
                                            "step" => step,
                                            "tactic" => tactic,
                                            "prover" => "Coq",
                                            "tactic_type" => tactic_type,
                                        ))
                                    end
                                end
                            end

                            # Extract premises/hypotheses
                            hyp_patterns = [
                                r"intros?\s+([a-zA-Z0-9_\s]+)",
                                r"pose\s+([a-zA-Z0-9_]+)\s*:=",
                                r"assert\s+\(([a-zA-Z0-9_]+):",
                            ]

                            for hyp_pattern in hyp_patterns
                                for hyp_match in eachmatch(Regex(hyp_pattern), proof_content)
                                    hyps = split(strip(hyp_match.captures[1]))
                                    for hyp in hyps
                                        if !isempty(hyp) && length(hyp) < 50
                                            push!(premises, Dict{String,Any}(
                                                "proof_id" => file_id,
                                                "premise" => String(hyp),
                                                "prover" => "Coq",
                                                "theorem" => name,
                                                "source" => "CoqGym",
                                            ))
                                        end
                                    end
                                end
                            end
                        end

                        file_id += 1
                    end
                catch
                    continue  # Skip problematic matches
                end
            end
        end

        return proof_states, tactics, premises, file_id - START_ID

    catch e
        println("  WARNING: Error processing $filepath: $e")
        return Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[], 0
    end
end

"""
    save_extracted_data(proof_states, tactics, premises, next_id)

Save extracted data with progress tracking. Uses atomic rename for safety.
"""
function save_extracted_data(proof_states, tactics, premises, next_id)
    mkpath(OUTPUT_DIR)

    temp_states = PROOF_STATES_FILE * ".tmp"
    temp_tactics = TACTICS_FILE * ".tmp"
    temp_premises = PREMISES_FILE * ".tmp"

    try
        # Save proof states
        open(temp_states, "w") do f
            for state in proof_states
                println(f, JSON3.write(state))
            end
        end

        # Save tactics
        open(temp_tactics, "w") do f
            for tactic in tactics
                println(f, JSON3.write(tactic))
            end
        end

        # Save premises
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
            "source" => "CoqGym_MAX",
            "extraction_date" => "2026-03-20",
            "proof_states_count" => length(proof_states),
            "tactics_count" => length(tactics),
            "premises_count" => length(premises),
            "start_id" => START_ID,
            "end_id" => next_id - 1,
            "extraction_method" => "comprehensive_regex",
        )

        open(STATS_FILE, "w") do f
            write(f, JSON3.write(stats))
        end

        println("  Saved progress: $(length(proof_states)) proofs, $(length(tactics)) tactics, $(length(premises)) premises")

    catch e
        println("  ERROR saving data: $e")
        # Clean up temp files
        for temp_file in [temp_states, temp_tactics, temp_premises]
            isfile(temp_file) && rm(temp_file)
        end
    end
end

"""
    max_extract_coqgym()

Maximum extraction from all CoqGym files.
"""
function max_extract_coqgym()
    println("MAXIMUM CoqGym Extraction")
    println("=" ^ 50)

    # Find ALL .v files
    coqgym_proofs_dir = joinpath(COQGYM_DIR, "coq_projects")

    if !isdir(coqgym_proofs_dir)
        println("ERROR: CoqGym directory not found: $coqgym_proofs_dir")
        return
    end

    # Get all .v files
    v_files = String[]
    for (root, _dirs, files) in walkdir(coqgym_proofs_dir)
        for file in files
            if endswith(file, ".v")
                push!(v_files, joinpath(root, file))
            end
        end
    end

    println("Found $(length(v_files)) Coq files to process")

    # Process files in batches
    all_proof_states = Dict{String,Any}[]
    all_tactics = Dict{String,Any}[]
    all_premises = Dict{String,Any}[]
    current_id = START_ID
    batch_size = 100

    for i in 1:batch_size:length(v_files)
        batch = v_files[i:min(i + batch_size - 1, length(v_files))]
        batch_num = div(i - 1, batch_size) + 1
        total_batches = div(length(v_files) - 1, batch_size) + 1
        println("Processing batch $batch_num/$total_batches ($(length(batch)) files)...")

        batch_results = Tuple{String,Int}[]
        for filepath in batch
            try
                proofs, tacs, prems, count = extract_file_proofs(filepath)
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
        if length(all_proof_states) >= 1000
            save_extracted_data(all_proof_states, all_tactics, all_premises, current_id)
            println("  Checkpoint saved: $(length(all_proof_states)) proofs so far")
        end
    end

    # Final save
    save_extracted_data(all_proof_states, all_tactics, all_premises, current_id)

    println("\nMAXIMUM Extraction Complete!")
    println("   Total Proofs: $(length(all_proof_states))")
    println("   Total Tactics: $(length(all_tactics))")
    println("   Total Premises: $(length(all_premises))")
    println("   ID Range: $START_ID - $(current_id - 1)")
end

if abspath(PROGRAM_FILE) == @__FILE__
    max_extract_coqgym()
end
