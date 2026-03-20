#!/usr/bin/env julia
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Comprehensive corpus merger for ECHIDNA v2.0

Merges all extracted proof corpora into unified training files.
"""

using JSON3
using Dates

const INPUT_DIR = "training_data"
const OUTPUT_DIR = "training_data"

# File patterns to merge
const FILE_PATTERNS = [
    # Original files
    ("proof_states", ["proof_states.jsonl", "proof_states_v2.jsonl"]),
    ("tactics", ["tactics.jsonl", "tactics_v2.jsonl"]),
    ("premises", ["premises.jsonl"]),
    
    # Metamath extraction
    ("proof_states", ["proof_states_metamath.jsonl"]),
    ("tactics", ["tactics_metamath.jsonl"]),
    
    # CoqGym extraction
    ("proof_states", ["proof_states_coqgym.jsonl"]),
    ("tactics", ["tactics_coqgym.jsonl"]),
    ("premises", ["premises_coqgym.jsonl"]),
    
    # mathlib4 extraction
    ("proof_states", ["proof_states_mathlib4.jsonl"]),
    ("tactics", ["tactics_mathlib4.jsonl"]),
]

function read_jsonl_lines(filepath::String)::Vector{Dict{String, Any}}
    """Read JSONL file line by line, handling parsing errors gracefully."""
    data = Dict{String, Any}[]
    
    if !isfile(filepath)
        @warn "File not found: $filepath"
        return data
    end
    
    try
        open(filepath, "r") do io
            for line in eachline(io)
                stripped = strip(line)
                isempty(stripped) && continue
                
                try
                    # Parse JSON line
                    entry = JSON3.read(stripped)
                    if entry isa Dict{String, Any}
                        push!(data, entry)
                    end
                catch e
                    @warn "Failed to parse line in $filepath: $e"
                    continue
                end
            end
        end
    catch e
        @error "Failed to read file $filepath: $e"
    end
    
    return data
end

function merge_files(file_type::String, file_patterns::Vector{String})::Vector{Dict{String, Any}}
    """Merge multiple JSONL files of the same type."""
    
    println("🔄 Merging $file_type files...")
    
    all_data = Dict{String, Any}[]
    seen_ids = Set{Int}()
    
    for pattern in file_patterns
        filepath = joinpath(INPUT_DIR, pattern)
        if isfile(filepath)
            println("  Reading: $pattern")
            data = read_jsonl_lines(filepath)
            
            # Deduplicate by ID
            for entry in data
                if haskey(entry, "id")
                    id = entry["id"]
                    if id isa Int && !(id in seen_ids)
                        push!(all_data, entry)
                        push!(seen_ids, id)
                    elseif id isa Int
                        @debug "Duplicate ID $id found, skipping"
                    end
                else
                    push!(all_data, entry)
                end
            end
            
            println("  Found $(length(data)) entries, $(length(all_data)) unique after merge")
        else
            @warn "File not found: $filepath"
        end
    end
    
    return all_data
end

function write_merged_file(data::Vector{Dict{String, Any}}, output_file::String)
    """Write merged data to output file."""
    
    if isempty(data)
        @warn "No data to write for $output_file"
        return
    end
    
    println("💾 Writing merged data to $output_file...")
    
    # Sort by ID if available
    if !isempty(data) && haskey(first(data), "id")
        sort!(data, by = x -> x["id"])
    end
    
    open(output_file, "w") do io
        for entry in data
            JSON3.write(io, entry)
            write(io, '\n')
        end
    end
    
    println("✅ Wrote $(length(data)) entries to $output_file")
end

function calculate_statistics(proof_states::Vector{Dict{String, Any}},
                            tactics::Vector{Dict{String, Any}},
                            premises::Vector{Dict{String, Any}})
    """Calculate comprehensive corpus statistics."""
    
    println("📊 Calculating corpus statistics...")
    
    # Count by prover
    prover_counts = Dict{String, Int}()
    for state in proof_states
        prover = get(state, "prover", "unknown")
        prover_counts[prover] = get(prover_counts, prover, 0) + 1
    end
    
    # Count tactics by prover
    tactic_prover_counts = Dict{String, Int}()
    for tactic in tactics
        prover = get(tactic, "prover", "unknown")
        tactic_prover_counts[prover] = get(tactic_prover_counts, prover, 0) + 1
    end
    
    # Unique theorems
    theorem_names = Set{String}()
    for state in proof_states
        theorem = get(state, "theorem", "")
        if !isempty(theorem)
            push!(theorem_names, theorem)
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
    
    stats = Dict{
        "version" => "v2.0-comprehensive",
        "merge_date" => string(Dates.now()),
        "total_proofs" => length(proof_states),
        "total_tactics" => length(tactics),
        "total_premises" => length(premises),
        "unique_theorems" => length(theorem_names),
        "unique_tactics" => length(tactic_names),
        "proofs_by_prover" => prover_counts,
        "tactics_by_prover" => tactic_prover_counts,
        "sources" => [
            "Original ECHIDNA corpus",
            "Metamath extraction",
            "CoqGym extraction",
            "mathlib4 extraction"
        ]
    }
    
    # Write statistics
    stats_file = joinpath(OUTPUT_DIR, "stats_comprehensive.json")
    open(stats_file, "w") do io
        JSON3.write(io, stats)
    end
    
    println("✅ Statistics written to $stats_file")
    
    return stats
end

function main()
    """Main merging function."""
    
    println("🚀 ECHIDNA Comprehensive Corpus Merger")
    println("="^50)
    
    # Organize file patterns by type
    proof_state_patterns = String[]
    tactic_patterns = String[]
    premise_patterns = String[]
    
    for (file_type, patterns) in FILE_PATTERNS
        if file_type == "proof_states"
            append!(proof_state_patterns, patterns)
        elseif file_type == "tactics"
            append!(tactic_patterns, patterns)
        elseif file_type == "premises"
            append!(premise_patterns, patterns)
        end
    end
    
    # Merge each file type
    proof_states = merge_files("proof_states", proof_state_patterns)
    tactics = merge_files("tactics", tactic_patterns)
    premises = merge_files("premises", premise_patterns)
    
    # Write merged files
    write_merged_file(proof_states, joinpath(OUTPUT_DIR, "proof_states_comprehensive.jsonl"))
    write_merged_file(tactics, joinpath(OUTPUT_DIR, "tactics_comprehensive.jsonl"))
    write_merged_file(premises, joinpath(OUTPUT_DIR, "premises_comprehensive.jsonl"))
    
    # Calculate and save statistics
    stats = calculate_statistics(proof_states, tactics, premises)
    
    println("\n🎉 Merging Complete!")
    println("📈 Final Statistics:")
    println("  Proofs: $(stats["total_proofs"])")
    println("  Tactics: $(stats["total_tactics"])")
    println("  Premises: $(stats["total_premises"])")
    println("  Unique Theorems: $(stats["unique_theorems"])")
    println("  Unique Tactics: $(stats["unique_tactics"])")
    println("  Provers: $(join(keys(stats["proofs_by_prover"]), ", "))")
    
    println("\n📁 Output files:")
    println("  - proof_states_comprehensive.jsonl")
    println("  - tactics_comprehensive.jsonl")
    println("  - premises_comprehensive.jsonl")
    println("  - stats_comprehensive.json")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end