#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Final Metamath proof extractor - simplified and robust.
# Extracts theorems from Metamath set.mm and converts to ECHIDNA training format.

using JSON3
using Dates

"""
    extract_theorems(file_path::String) -> Vector{Dict{String,String}}

Extract theorems from a Metamath set.mm file. Each theorem is returned as a Dict
with keys "name", "statement", and "proof".
"""
function extract_theorems(file_path::String)::Vector{Dict{String,String}}
    theorems = Dict{String,String}[]

    # Pattern: theorem_name \$p statement \$= proof \$.
    pattern = r"^\s*([a-zA-Z0-9._-]+)\s+\$p\s+([^$]+)\$=\s*([^$]+)\$\."m

    content = read(file_path, String)

    for m in eachmatch(pattern, content)
        name = strip(m.captures[1])
        statement = strip(m.captures[2])
        proof = strip(m.captures[3])

        if !isempty(name) && !isempty(proof)
            push!(theorems, Dict(
                "name" => name,
                "statement" => statement,
                "proof" => proof
            ))
        end
    end

    return theorems
end

"""
    save_as_training_data(theorems::Vector{Dict{String,String}}) -> Int

Save extracted theorems as JSONL training data files (proof states and tactics).
Returns the number of theorems saved.
"""
function save_as_training_data(theorems::Vector{Dict{String,String}})::Int
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]

    for (i, theorem) in enumerate(theorems)
        # Proof state
        state = Dict{String,Any}(
            "id" => i - 1 + 1000,  # Start from 1000 to avoid conflicts
            "prover" => "Metamath",
            "theorem" => theorem["name"],
            "goal" => theorem["statement"],
            "context" => Any[],
            "source" => "Metamath",
            "proof_steps" => length(split(theorem["proof"]))
        )
        push!(proof_states, state)

        # Tactic
        tactic = Dict{String,Any}(
            "proof_id" => i - 1 + 1000,
            "step" => 1,
            "tactic" => "metamath_prove",
            "prover" => "Metamath",
            "proof_text" => theorem["proof"]
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
        "version" => "v2.0-metamath-final",
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
        println("  Sample theorem: $(theorems[1]["name"])")
        proof_preview = theorems[1]["proof"]
        println("  Sample proof: $(first(proof_preview, 50))...")
    end
    println("  Files saved: proof_states_metamath.jsonl, tactics_metamath.jsonl")

    return length(theorems)
end

"""
    main()

Entry point. Reads Metamath set.mm, extracts theorems, and saves training data.
"""
function main()
    println("Metamath Proof Extractor (Final)")
    println("===============================")

    file_path = "external_corpora/metamath/set.mm"

    if !isfile(file_path)
        println("Error: File not found: $file_path")
        return 1
    end

    println("\nExtracting from $file_path...")
    theorems = extract_theorems(file_path)
    println("Found $(length(theorems)) theorems")

    if !isempty(theorems)
        println("\nFirst 10 theorems:")
        for (i, theorem) in enumerate(first(theorems, 10))
            println("  $i. $(theorem["name"])")
        end
    end

    println("\nSaving training data...")
    save_as_training_data(theorems)

    return 0
end

main()
