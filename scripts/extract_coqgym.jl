#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Extract proofs from CoqGym corpus and convert to ECHIDNA training format.
# CoqGym contains high-quality Coq proofs that improve corpus diversity.

using JSON3

# Configuration
const COQGYM_DIR = "external_corpora/CoqGym"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_coqgym.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_coqgym.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_coqgym.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_coqgym.json")

# Start ID after existing data (Metamath ended at 47165 + original 108 = 47273)
const START_ID = 47274

"""
    extract_coqgym_proofs() -> Tuple{Vector, Vector, Vector}

Extract proofs from CoqGym corpus. Returns (proof_states, tactics, premises).
"""
function extract_coqgym_proofs()
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    current_id = START_ID

    # Look for CoqGym proof files
    coqgym_proofs_dir = joinpath(COQGYM_DIR, "coq_projects")

    if !isdir(coqgym_proofs_dir)
        println("CoqGym proofs directory not found: $coqgym_proofs_dir")
        return Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    end

    # Find .v files (Coq source files)
    v_files = String[]
    for (root, dirs, files) in walkdir(coqgym_proofs_dir)
        for file in files
            if endswith(file, ".v")
                push!(v_files, joinpath(root, file))
            end
        end
    end

    println("Found $(length(v_files)) Coq files in CoqGym")

    # Simple extraction - look for theorems and proofs
    theorem_pattern = r"Theorem\s+([a-zA-Z0-9_]+)\s*:\s*(.*?)\s*\."s
    proof_pattern = r"Proof\.(.*?)Q\."s
    tactic_pattern = r"\.\s*([a-zA-Z0-9_]+)"

    for v_file in first(v_files, 100)  # Limit to first 100 files for now
        try
            content = read(v_file, String)

            # Extract theorems
            for theorem_match in eachmatch(theorem_pattern, content)
                theorem_name = strip(theorem_match.captures[1])
                theorem_statement = strip(theorem_match.captures[2])

                if !isempty(theorem_name) && !isempty(theorem_statement)
                    # Create proof state
                    proof_state = Dict{String,Any}(
                        "id" => current_id,
                        "prover" => "Coq",
                        "theorem" => theorem_name,
                        "goal" => theorem_statement,
                        "context" => Any[]
                    )
                    push!(proof_states, proof_state)

                    # Look for proof and extract tactics
                    proof_start = theorem_match.offset + length(theorem_match.match)
                    remaining_content = content[min(proof_start, end):end]
                    proof_m = match(proof_pattern, remaining_content)

                    if !isnothing(proof_m)
                        proof_content = proof_m.captures[1]

                        # Extract tactics (simplified)
                        for (step, tactic_match) in enumerate(eachmatch(tactic_pattern, proof_content))
                            tactic = strip(tactic_match.captures[1])

                            if !isempty(tactic)
                                push!(tactics, Dict{String,Any}(
                                    "proof_id" => current_id,
                                    "step" => step,
                                    "tactic" => tactic,
                                    "prover" => "Coq"
                                ))
                            end
                        end

                        # Extract premises (hypotheses)
                        hyp_pattern = r"intros?\s+([a-zA-Z0-9_\s]+)"
                        for hyp_match in eachmatch(hyp_pattern, proof_content)
                            hyps = split(strip(hyp_match.captures[1]))
                            for hyp in hyps
                                push!(premises, Dict{String,Any}(
                                    "proof_id" => current_id,
                                    "premise" => String(hyp),
                                    "prover" => "Coq",
                                    "theorem" => theorem_name
                                ))
                            end
                        end
                    end

                    current_id += 1
                end
            end
        catch e
            println("Warning: Error processing $v_file: $e")
        end
    end

    return proof_states, tactics, premises
end

"""
    save_extracted_data(proof_states, tactics, premises)

Save extracted data to JSONL files and write statistics.
"""
function save_extracted_data(proof_states::Vector, tactics::Vector, premises::Vector)
    # Create output directory
    mkpath(OUTPUT_DIR)

    # Save proof states
    open(PROOF_STATES_FILE, "w") do f
        for state in proof_states
            println(f, JSON3.write(state))
        end
    end

    # Save tactics
    open(TACTICS_FILE, "w") do f
        for tactic in tactics
            println(f, JSON3.write(tactic))
        end
    end

    # Save premises
    open(PREMISES_FILE, "w") do f
        for premise in premises
            println(f, JSON3.write(premise))
        end
    end

    # Save statistics
    stats = Dict{String,Any}(
        "source" => "CoqGym",
        "extraction_date" => "2026-03-20",
        "proof_states_count" => length(proof_states),
        "tactics_count" => length(tactics),
        "premises_count" => length(premises),
        "start_id" => START_ID,
        "end_id" => isempty(proof_states) ? START_ID : START_ID + length(proof_states) - 1
    )

    open(STATS_FILE, "w") do f
        JSON3.pretty(f, stats)
    end

    println("Saved $(length(proof_states)) proof states to $PROOF_STATES_FILE")
    println("Saved $(length(tactics)) tactics to $TACTICS_FILE")
    println("Saved $(length(premises)) premises to $PREMISES_FILE")
    println("Saved statistics to $STATS_FILE")
end

"""
    merge_with_existing_data()

Print merge instructions for combining CoqGym data with the main corpus.
"""
function merge_with_existing_data()
    println("Merging CoqGym data with existing corpus...")
    println("CoqGym data extraction complete!")
    println("To merge with main corpus, run:")
    println("   julia scripts/merge_training_data.jl")
end

"""
    main()

Main extraction function. Extracts proofs from CoqGym and saves training data.
"""
function main()
    println("ECHIDNA CoqGym Extraction")
    println("=" ^ 40)

    # Extract proofs from CoqGym
    proof_states, tactics, premises = extract_coqgym_proofs()

    if isempty(proof_states)
        println("No proofs extracted from CoqGym")
        return
    end

    # Save extracted data
    save_extracted_data(proof_states, tactics, premises)

    # Merge with existing data
    merge_with_existing_data()

    println("\nExtraction Summary:")
    println("   Proofs: $(length(proof_states))")
    println("   Tactics: $(length(tactics))")
    println("   Premises: $(length(premises))")
    println("   ID Range: $START_ID - $(START_ID + length(proof_states) - 1)")
end

main()
