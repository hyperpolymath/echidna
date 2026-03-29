#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Extract proofs from Lean mathlib4 corpus and convert to ECHIDNA training format.
# mathlib4 contains high-quality Lean proofs that improve corpus diversity.

using JSON3

# Configuration
const MATHLIB4_DIR = "external_corpora/mathlib4"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_mathlib4.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_mathlib4.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_mathlib4.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_mathlib4.json")

# Start ID after CoqGym (47274 + 14 = 47288)
const START_ID = 47288

"""
    extract_mathlib4_proofs() -> Tuple{Vector, Vector, Vector}

Extract proofs from mathlib4 corpus. Returns (proof_states, tactics, premises).
"""
function extract_mathlib4_proofs()
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    current_id = START_ID

    # Look for mathlib4 proof files
    mathlib4_proofs_dir = joinpath(MATHLIB4_DIR, "Mathlib")

    if !isdir(mathlib4_proofs_dir)
        println("mathlib4 proofs directory not found: $mathlib4_proofs_dir")
        return Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    end

    # Find .lean files
    lean_files = String[]
    for (root, dirs, files) in walkdir(mathlib4_proofs_dir)
        for file in files
            if endswith(file, ".lean")
                push!(lean_files, joinpath(root, file))
            end
        end
    end

    println("Found $(length(lean_files)) Lean files in mathlib4")

    # Simple extraction - look for theorems and proofs
    theorem_pattern = r"theorem\s+([a-zA-Z0-9_]+)\s*(.*?)\s*:=\s*by"s
    lemma_pattern = r"lemma\s+([a-zA-Z0-9_]+)\s*(.*?)\s*:=\s*by"s

    for lean_file in first(lean_files, 50)  # Limit to first 50 files for now
        try
            content = read(lean_file, String)

            # Extract theorems and lemmas
            for (pattern, proof_type) in [(theorem_pattern, "theorem"), (lemma_pattern, "lemma")]
                for m in eachmatch(pattern, content)
                    name = strip(m.captures[1])
                    statement = strip(m.captures[2])

                    if !isempty(name) && !isempty(statement)
                        # Create proof state
                        proof_state = Dict{String,Any}(
                            "id" => current_id,
                            "prover" => "Lean",
                            "theorem" => name,
                            "goal" => statement,
                            "context" => Any[]
                        )
                        push!(proof_states, proof_state)

                        # Look for proof tactics (simplified)
                        proof_start = m.offset + length(m.match)
                        remaining_content = content[min(proof_start, end):end]

                        # Extract tactics from the "by" clause
                        by_match = match(r"by\s+([^\n]+)", remaining_content)

                        if !isnothing(by_match)
                            tactics_str = strip(by_match.captures[1])
                            # Split by tactic separators
                            individual_tactics = split(tactics_str, r"[\s,]+")

                            for (step, tactic) in enumerate(individual_tactics)
                                if !isempty(tactic)
                                    push!(tactics, Dict{String,Any}(
                                        "proof_id" => current_id,
                                        "step" => step,
                                        "tactic" => String(tactic),
                                        "prover" => "Lean"
                                    ))
                                end
                            end
                        end

                        current_id += 1
                    end
                end
            end
        catch e
            println("Warning: Error processing $lean_file: $e")
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
        "source" => "mathlib4",
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
    main()

Main extraction function. Extracts proofs from mathlib4 and saves training data.
"""
function main()
    println("ECHIDNA mathlib4 Extraction")
    println("=" ^ 40)

    # Extract proofs from mathlib4
    proof_states, tactics, premises = extract_mathlib4_proofs()

    if isempty(proof_states)
        println("No proofs extracted from mathlib4")
        return
    end

    # Save extracted data
    save_extracted_data(proof_states, tactics, premises)

    println("\nExtraction Summary:")
    println("   Proofs: $(length(proof_states))")
    println("   Tactics: $(length(tactics))")
    println("   Premises: $(length(premises))")
    println("   ID Range: $START_ID - $(START_ID + length(proof_states) - 1)")
end

main()
