#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Final complete merge - ensure ALL data is included.
# Deduplicates and merges proof states, tactics, and premises from all source
# files into single COMPLETE output files with statistics.

using JSON3

"""
    read_jsonl_file(filepath::String) -> Vector{Dict{String,Any}}

Read a JSONL file and return a vector of parsed dictionaries. Returns an empty
vector if the file does not exist or a line fails to parse.
"""
function read_jsonl_file(filepath::String)::Vector{Dict{String,Any}}
    data = Dict{String,Any}[]
    if !isfile(filepath)
        return data
    end
    try
        open(filepath, "r") do f
            for line in eachline(f)
                stripped = strip(line)
                if !isempty(stripped)
                    try
                        push!(data, JSON3.read(stripped, Dict{String,Any}))
                    catch
                        continue
                    end
                end
            end
        end
    catch
        # File not found or read error
    end
    return data
end

"""
    merge_all_proof_data() -> Int

Merge all proof state JSONL files, deduplicating by ID. Returns total count.
"""
function merge_all_proof_data()::Int
    println("Merging ALL proof data...")

    # Find all proof state files
    files = [
        "training_data/proof_states.jsonl",
        "training_data/proof_states_v2.jsonl",
        "training_data/proof_states_2026-03-20.jsonl",
        "training_data/proof_states_metamath.jsonl",
        "training_data/proof_states_coqgym.jsonl",
        "training_data/proof_states_mathlib4.jsonl",
        "training_data/proof_states_coqgym_max.jsonl",
        "training_data/proof_states_mathlib4_max.jsonl",
    ]

    all_proofs = Dict{String,Any}[]
    seen_ids = Set{Int}()

    for filepath in files
        if isfile(filepath)
            println("  Reading $filepath...")
            proofs = read_jsonl_file(filepath)
            println("    Found $(length(proofs)) proofs")

            # Deduplicate by ID
            for proof in proofs
                if haskey(proof, "id") && !(proof["id"] in seen_ids)
                    push!(all_proofs, proof)
                    push!(seen_ids, proof["id"])
                elseif !haskey(proof, "id")
                    # Generate new ID if missing
                    new_id = isempty(seen_ids) ? 1 : maximum(seen_ids) + 1
                    proof["id"] = new_id
                    push!(all_proofs, proof)
                    push!(seen_ids, new_id)
                end
            end
        end
    end

    println("  Total unique proofs: $(length(all_proofs))")
    if !isempty(all_proofs)
        ids = [p["id"] for p in all_proofs]
        println("  ID range: $(minimum(ids)) - $(maximum(ids))")
    end

    # Sort by ID
    sort!(all_proofs; by=x -> x["id"])

    # Save
    open("training_data/proof_states_COMPLETE.jsonl", "w") do f
        for proof in all_proofs
            println(f, JSON3.write(proof))
        end
    end

    return length(all_proofs)
end

"""
    merge_all_tactics_data() -> Int

Merge all tactics JSONL files. Returns total count.
"""
function merge_all_tactics_data()::Int
    println("Merging ALL tactics data...")

    files = [
        "training_data/tactics.jsonl",
        "training_data/tactics_v2.jsonl",
        "training_data/tactics_2026-03-20.jsonl",
        "training_data/tactics_metamath.jsonl",
        "training_data/tactics_coqgym.jsonl",
        "training_data/tactics_mathlib4.jsonl",
        "training_data/tactics_coqgym_max.jsonl",
        "training_data/tactics_mathlib4_max.jsonl",
    ]

    all_tactics = Dict{String,Any}[]

    for filepath in files
        if isfile(filepath)
            println("  Reading $filepath...")
            tactics = read_jsonl_file(filepath)
            println("    Found $(length(tactics)) tactics")
            append!(all_tactics, tactics)
        end
    end

    println("  Total tactics: $(length(all_tactics))")

    # Save
    open("training_data/tactics_COMPLETE.jsonl", "w") do f
        for tactic in all_tactics
            println(f, JSON3.write(tactic))
        end
    end

    return length(all_tactics)
end

"""
    merge_all_premises_data() -> Int

Merge all premises JSONL files. Returns total count.
"""
function merge_all_premises_data()::Int
    println("Merging ALL premises data...")

    files = [
        "training_data/premises.jsonl",
        "training_data/premises_2026-03-20.jsonl",
        "training_data/premises_coqgym.jsonl",
        "training_data/premises_coqgym_max.jsonl",
    ]

    all_premises = Dict{String,Any}[]

    for filepath in files
        if isfile(filepath)
            println("  Reading $filepath...")
            premises = read_jsonl_file(filepath)
            println("    Found $(length(premises)) premises")
            append!(all_premises, premises)
        end
    end

    println("  Total premises: $(length(all_premises))")

    # Save
    open("training_data/premises_COMPLETE.jsonl", "w") do f
        for premise in all_premises
            println(f, JSON3.write(premise))
        end
    end

    return length(all_premises)
end

"""
    calculate_final_stats() -> Dict{String,Any}

Calculate and save final statistics from the COMPLETE output files.
"""
function calculate_final_stats()::Dict{String,Any}
    println("Calculating final statistics...")

    # Read the complete files
    proofs = read_jsonl_file("training_data/proof_states_COMPLETE.jsonl")
    tactics = read_jsonl_file("training_data/tactics_COMPLETE.jsonl")
    premises = read_jsonl_file("training_data/premises_COMPLETE.jsonl")

    # Count by prover
    prover_counts = Dict{String,Int}()
    for proof in proofs
        prover = get(proof, "prover", "unknown")
        prover_counts[prover] = get(prover_counts, prover, 0) + 1
    end

    tactic_prover_counts = Dict{String,Int}()
    for tactic in tactics
        prover = get(tactic, "prover", "unknown")
        tactic_prover_counts[prover] = get(tactic_prover_counts, prover, 0) + 1
    end

    # Unique theorems
    theorems = Set{String}()
    for proof in proofs
        theorem = get(proof, "theorem", "")
        if !isempty(theorem)
            push!(theorems, theorem)
        end
    end

    # Unique tactics
    tactic_names = Set{String}()
    for tactic in tactics
        tactic_name = get(tactic, "tactic", "")
        if !isempty(tactic_name)
            push!(tactic_names, tactic_name)
        end
    end

    ids_with_id = [p["id"] for p in proofs if haskey(p, "id")]

    stats = Dict{String,Any}(
        "version" => "v2.0-COMPLETE",
        "merge_date" => "2026-03-20",
        "total_proofs" => length(proofs),
        "total_tactics" => length(tactics),
        "total_premises" => length(premises),
        "unique_theorems" => length(theorems),
        "unique_tactics" => length(tactic_names),
        "proofs_by_prover" => prover_counts,
        "tactics_by_prover" => tactic_prover_counts,
        "id_range" => Dict{String,Any}(
            "min" => isempty(ids_with_id) ? 0 : minimum(ids_with_id),
            "max" => isempty(ids_with_id) ? 0 : maximum(ids_with_id)
        ),
        "sources" => [
            "Original ECHIDNA corpus",
            "Metamath extraction",
            "CoqGym extraction (basic)",
            "CoqGym extraction (comprehensive)",
            "mathlib4 extraction (basic)",
            "mathlib4 extraction (comprehensive)"
        ]
    )

    open("training_data/stats_COMPLETE.json", "w") do f
        JSON3.pretty(f, stats)
    end

    println("  Total proofs: $(length(proofs))")
    println("  Total tactics: $(length(tactics))")
    println("  Total premises: $(length(premises))")
    println("  Unique theorems: $(length(theorems))")
    println("  Unique tactics: $(length(tactic_names))")
    println("  Provers: $(length(prover_counts))")

    return stats
end

"""
    main()

Main merge function. Merges all proof data, tactics, and premises, then
calculates final statistics.
"""
function main()
    println("FINAL COMPLETE MERGE")
    println("=" ^ 50)

    # Merge all data
    proof_count = merge_all_proof_data()
    tactic_count = merge_all_tactics_data()
    premise_count = merge_all_premises_data()

    # Calculate statistics
    stats = calculate_final_stats()

    println("\nCOMPLETE MERGE FINISHED!")
    println("   Proofs: $proof_count")
    println("   Tactics: $tactic_count")
    println("   Premises: $premise_count")
    println("   Unique Theorems: $(stats["unique_theorems"])")
    println("   Unique Tactics: $(stats["unique_tactics"])")
    println("   Provers: $(length(stats["proofs_by_prover"]))")

    println("\nFiles created:")
    println("   training_data/proof_states_COMPLETE.jsonl")
    println("   training_data/tactics_COMPLETE.jsonl")
    println("   training_data/premises_COMPLETE.jsonl")
    println("   training_data/stats_COMPLETE.json")
end

main()
