#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Merge training data files for ECHIDNA corpus expansion

using JSON3
using Dates

const TRAINING_DIR = "training_data"

"""
Merge two JSONL files, avoiding duplicates by ID
"""
function merge_jsonl_files(file1::String, file2::String, output_file::String, key_field::String="id")
    # Read existing data
    existing_data = Dict{Any, Any}()
    if isfile(file1)
        for line in eachline(file1)
            if !isempty(strip(line))
                try
                    record = JSON3.read(line)
                    key = get(record, key_field, nothing)
                    if key !== nothing
                        existing_data[key] = record
                    end
                catch e
                    @warn "Error parsing line in $file1: $line" exception=e
                end
            end
        end
    end

    # Read new data and merge
    new_count = 0
    if isfile(file2)
        for line in eachline(file2)
            if !isempty(strip(line))
                try
                    record = JSON3.read(line)
                    key = get(record, key_field, nothing)
                    if key !== nothing && !haskey(existing_data, key)
                        existing_data[key] = record
                        new_count += 1
                    end
                catch e
                    @warn "Error parsing line in $file2: $line" exception=e
                end
            end
        end
    end

    # Write merged data
    mkpath(dirname(output_file))
    open(output_file, "w") do io
        for (key, record) in existing_data
            println(io, JSON3.write(record))
        end
    end

    return (length(existing_data), new_count)
end

"""
Merge training data from backup and new extraction
"""
function merge_training_data()
    println("ECHIDNA Training Data Merger")
    println("==============================")

    # Backup current files
    backup_date = Dates.format(now(), "yyyy-mm-dd")
    println("\nBacking up current data to *_$backup_date.jsonl...")
    
    for file in ["proof_states", "tactics", "premises"]
        if isfile(joinpath(TRAINING_DIR, file * ".jsonl")) && !isfile(joinpath(TRAINING_DIR, file * "_$backup_date.jsonl"))
            cp(joinpath(TRAINING_DIR, file * ".jsonl"), joinpath(TRAINING_DIR, file * "_$backup_date.jsonl"), force=true)
        end
    end

    # Merge proof states
    println("\nMerging proof_states.jsonl...")
    total_proofs, new_proofs = merge_jsonl_files(
        joinpath(TRAINING_DIR, "proof_states_v2.jsonl"),  # Original 332 proofs
        joinpath(TRAINING_DIR, "proof_states.jsonl"),     # New 108 proofs
        joinpath(TRAINING_DIR, "proof_states_merged.jsonl"),
        "id"
    )
    println("  Total proofs: $total_proofs ($new_proofs new)")

    # Merge tactics
    println("\nMerging tactics.jsonl...")
    total_tactics, new_tactics = merge_jsonl_files(
        joinpath(TRAINING_DIR, "tactics_v2.jsonl"),       # Original 1603 tactics
        joinpath(TRAINING_DIR, "tactics.jsonl"),          # New 586 tactics
        joinpath(TRAINING_DIR, "tactics_merged.jsonl"),
        "id"
    )
    println("  Total tactics: $total_tactics ($new_tactics new)")

    # For premises, we can just concatenate (no ID conflicts)
    println("\nMerging premises.jsonl...")
    premises_count = 0
    open(joinpath(TRAINING_DIR, "premises_merged.jsonl"), "w") do io
        if isfile(joinpath(TRAINING_DIR, "premises_v2.jsonl"))
            for line in eachline(joinpath(TRAINING_DIR, "premises_v2.jsonl"))
                if !isempty(strip(line))
                    println(io, line)
                    premises_count += 1
                end
            end
        end
        if isfile(joinpath(TRAINING_DIR, "premises.jsonl"))
            for line in eachline(joinpath(TRAINING_DIR, "premises.jsonl"))
                if !isempty(strip(line))
                    println(io, line)
                    premises_count += 1
                end
            end
        end
    end
    println("  Total premises: $premises_count")

    # Update stats
    println("\nUpdating stats.json...")
    stats = Dict(
        "version" => "v2.0-merged",
        "total_proofs" => total_proofs,
        "total_tactics" => total_tactics,
        "total_premises" => premises_count,
        "unique_theorems" => min(285 + new_proofs, total_proofs),  # Conservative estimate
        "extraction_date" => Dates.now(),
        "merged_from" => ["v1.3.1-expanded (332 proofs)", "v2.0-extraction (108 proofs)"]
    )

    open(joinpath(TRAINING_DIR, "stats_merged.json"), "w") do io
        JSON3.pretty(io, stats)
    end

    println("\n✓ Merge complete!")
    println("\nMerged files created:")
    println("  - $(joinpath(TRAINING_DIR, "proof_states_merged.jsonl")) ($total_proofs proofs)")
    println("  - $(joinpath(TRAINING_DIR, "tactics_merged.jsonl")) ($total_tactics tactics)")
    println("  - $(joinpath(TRAINING_DIR, "premises_merged.jsonl")) ($premises_count premises)")
    println("  - $(joinpath(TRAINING_DIR, "stats_merged.json"))")
    println("\nTo use the merged data:")
    println("  mv $(joinpath(TRAINING_DIR, "proof_states_merged.jsonl")) $(joinpath(TRAINING_DIR, "proof_states.jsonl"))")
    println("  mv $(joinpath(TRAINING_DIR, "tactics_merged.jsonl")) $(joinpath(TRAINING_DIR, "tactics.jsonl"))")
    println("  mv $(joinpath(TRAINING_DIR, "premises_merged.jsonl")) $(joinpath(TRAINING_DIR, "premises.jsonl"))")
    println("  mv $(joinpath(TRAINING_DIR, "stats_merged.json")) $(joinpath(TRAINING_DIR, "stats.json"))")

    return (total_proofs, total_tactics, premises_count)
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    merge_training_data()
end
