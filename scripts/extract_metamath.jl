#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Metamath proof extractor.
# Line-by-line extraction of theorems from Metamath set.mm into ECHIDNA training format.

using JSON3
using Dates

"""
    Theorem

Represents a single Metamath theorem with its name, statement, and proof text.
"""
struct Theorem
    name::String
    statement::String
    proof::String
end

"""
    extract_theorems(file_path::String) -> Vector{Theorem}

Extract theorems from a Metamath set.mm file by scanning line-by-line for `\$p`
declarations, extracting the statement and proof portions.
"""
function extract_theorems(file_path::String)::Vector{Theorem}
    theorems = Theorem[]

    open(file_path, "r") do f
        for line in eachline(f)
            # Skip comment blocks and empty lines
            if startswith(line, "\$( ") || startswith(line, "\$)") || isempty(strip(line))
                continue
            end

            # Theorem declaration line (contains $p)
            if occursin("\$p", line)
                # Extract theorem name (before $p)
                parts = split(line, "\$p"; limit=2)
                if length(parts) > 1
                    name_part = strip(parts[1])
                    # Remove any trailing $.
                    name_part = replace(name_part, r"\$\." => "")
                    current_name = strip(name_part)

                    # Extract statement (between $p and $=)
                    statement_part = parts[2]
                    statement_match = match(r"^\s*([^$]+)\$=", statement_part)
                    current_statement = if !isnothing(statement_match)
                        strip(statement_match.captures[1])
                    else
                        ""
                    end

                    # Extract proof (after $=)
                    proof_match = match(r"\$=\s*([^$]+)\$\.", statement_part)
                    if !isnothing(proof_match)
                        current_proof = strip(proof_match.captures[1])

                        # Save theorem
                        if !isempty(current_name) && !isempty(current_proof)
                            push!(theorems, Theorem(current_name, current_statement, current_proof))
                        end
                    end
                end
            end
        end
    end

    return theorems
end

"""
    save_as_training_data(theorems::Vector{Theorem}) -> Int

Save extracted theorems as JSONL training data files (proof states and tactics).
Returns the number of theorems saved.
"""
function save_as_training_data(theorems::Vector{Theorem})::Int
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]

    for (i, theorem) in enumerate(theorems)
        # Proof state
        state = Dict{String,Any}(
            "id" => i - 1 + 1000,  # Start from 1000 to avoid conflicts
            "prover" => "Metamath",
            "theorem" => theorem.name,
            "goal" => theorem.statement,
            "context" => Any[],
            "source" => "Metamath",
            "proof_steps" => length(split(theorem.proof))
        )
        push!(proof_states, state)

        # Tactic
        tactic = Dict{String,Any}(
            "proof_id" => i - 1 + 1000,
            "step" => 1,
            "tactic" => "metamath_prove",
            "prover" => "Metamath",
            "proof_text" => theorem.proof
        )
        push!(tactics, tactic)
    end

    # Save to files
    training_dir = "training_data"
    mkpath(training_dir)

    open(joinpath(training_dir, "proof_states_metamath.jsonl"), "w") do f
        for state in proof_states
            println(f, JSON3.write(state))
        end
    end

    open(joinpath(training_dir, "tactics_metamath.jsonl"), "w") do f
        for tactic in tactics
            println(f, JSON3.write(tactic))
        end
    end

    # Save stats
    stats = Dict{String,Any}(
        "version" => "v2.0-metamath-python",
        "extraction_date" => string(now()),
        "total_proofs" => length(theorems),
        "total_tactics" => length(theorems),
        "source" => "Metamath set.mm",
        "prover" => "Metamath"
    )

    open(joinpath(training_dir, "stats_metamath.json"), "w") do f
        JSON3.pretty(f, stats)
    end

    println("Extracted $(length(theorems)) theorems from Metamath")
    if !isempty(theorems)
        println("  Sample theorem: $(theorems[1].name)")
    end
    println("  Files saved: proof_states_metamath.jsonl, tactics_metamath.jsonl")

    return length(theorems)
end

"""
    main()

Entry point. Reads Metamath set.mm, extracts theorems line-by-line, and saves
training data.
"""
function main()
    println("Metamath Proof Extractor")
    println("========================")

    file_path = "external_corpora/metamath/set.mm"

    if !isfile(file_path)
        println("Error: File not found: $file_path")
        return 1
    end

    println("\nExtracting from $file_path...")
    theorems = extract_theorems(file_path)
    println("Found $(length(theorems)) theorems")

    if !isempty(theorems)
        println("\nFirst few theorems:")
        for (i, theorem) in enumerate(first(theorems, 5))
            println("  $i. $(theorem.name)")
        end
    end

    println("\nSaving training data...")
    save_as_training_data(theorems)

    return 0
end

main()
