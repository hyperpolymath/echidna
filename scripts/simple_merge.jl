#!/usr/bin/env julia
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Simple corpus merger using manual JSON parsing (like original scripts).
"""

using Dates

const INPUT_DIR = "training_data"
const OUTPUT_DIR = "training_data"

# Simple JSON-like parser for our specific format
function parse_jsonl_line(line::String)::Dict{String, Any}
    entry = Dict{String, Any}()
    
    # Extract ID
    id_match = match(r"\"id\":(\d+)", line)
    if id_match !== nothing
        entry["id"] = parse(Int, id_match.captures[1])
    end
    
    # Extract prover
    prover_match = match(r"\"prover\":\"([^\"]+)\"", line)
    if prover_match !== nothing
        entry["prover"] = prover_match.captures[1]
    end
    
    # Extract theorem
    theorem_match = match(r"\"theorem\":\"([^\"]+)\"", line)
    if theorem_match !== nothing
        entry["theorem"] = theorem_match.captures[1]
    end
    
    # Extract goal
    goal_match = match(r"\"goal\":\"([^\"]+)\"", line)
    if goal_match !== nothing
        entry["goal"] = goal_match.captures[1]
    end
    
    # Extract proof_id
    proof_id_match = match(r"\"proof_id\":(\d+)", line)
    if proof_id_match !== nothing
        entry["proof_id"] = parse(Int, proof_id_match.captures[1])
    end
    
    # Extract step
    step_match = match(r"\"step\":(\d+)", line)
    if step_match !== nothing
        entry["step"] = parse(Int, step_match.captures[1])
    end
    
    # Extract tactic
    tactic_match = match(r"\"tactic\":\"([^\"]+)\"", line)
    if tactic_match !== nothing
        entry["tactic"] = tactic_match.captures[1]
    end
    
    # Extract premise
    premise_match = match(r"\"premise\":\"([^\"]+)\"", line)
    if premise_match !== nothing
        entry["premise"] = premise_match.captures[1]
    end
    
    return entry
end

function read_simple_jsonl(filepath::String)::Vector{Dict{String, Any}}
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
                
                entry = parse_jsonl_line(stripped)
                if !isempty(entry)
                    push!(data, entry)
                end
            end
        end
    catch e
        @error "Failed to read file $filepath: $e"
    end
    
    return data
end

function merge_files_simple(file_patterns::Vector{String})::Vector{Dict{String, Any}}
    """Merge files using simple parsing."""
    
    all_data = Dict{String, Any}[]
    seen_ids = Set{Int}()
    
    for pattern in file_patterns
        filepath = joinpath(INPUT_DIR, pattern)
        if isfile(filepath)
            println("  Reading: $pattern")
            data = read_simple_jsonl(filepath)
            
            # Deduplicate by ID
            for entry in data
                if haskey(entry, "id") && entry["id"] isa Int
                    id = entry["id"]
                    if !(id in seen_ids)
                        push!(all_data, entry)
                        push!(seen_ids, id)
                    end
                elseif haskey(entry, "proof_id") && entry["proof_id"] isa Int
                    id = entry["proof_id"]
                    if !(id in seen_ids)
                        push!(all_data, entry)
                        push!(seen_ids, id)
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

function write_simple_jsonl(data::Vector{Dict{String, Any}}, output_file::String)
    """Write data in simple JSONL format."""
    
    if isempty(data)
        @warn "No data to write for $output_file"
        return
    end
    
    println("💾 Writing to $output_file...")
    
    open(output_file, "w") do io
        for entry in data
            # Simple JSON writing
            write(io, "{")
            first = true
            
            for (key, value) in entry
                if !first
                    write(io, ", ")
                end
                write(io, "\"$key\":")
                
                if value isa String
                    # Escape quotes
                    escaped = replace(value, "\"" => "\\\"")
                    write(io, "\"$escaped\"")
                elseif value isa Int
                    write(io, "$value")
                else
                    write(io, "\"$value\"")
                end
                
                first = false
            end
            
            write(io, "}\n")
        end
    end
    
    println("✅ Wrote $(length(data)) entries")
end

function main()
    """Main function."""
    
    println("🚀 Simple ECHIDNA Corpus Merger")
    println("="^40)
    
    # Proof states files
    println("🔄 Merging proof states...")
    proof_state_files = [
        "proof_states.jsonl",
        "proof_states_v2.jsonl", 
        "proof_states_metamath.jsonl",
        "proof_states_coqgym.jsonl",
        "proof_states_mathlib4.jsonl"
    ]
    proof_states = merge_files_simple(proof_state_files)
    write_simple_jsonl(proof_states, joinpath(OUTPUT_DIR, "proof_states_merged.jsonl"))
    
    # Tactics files
    println("🔄 Merging tactics...")
    tactic_files = [
        "tactics.jsonl",
        "tactics_v2.jsonl",
        "tactics_metamath.jsonl",
        "tactics_coqgym.jsonl",
        "tactics_mathlib4.jsonl"
    ]
    tactics = merge_files_simple(tactic_files)
    write_simple_jsonl(tactics, joinpath(OUTPUT_DIR, "tactics_merged.jsonl"))
    
    # Premises files
    println("🔄 Merging premises...")
    premise_files = [
        "premises.jsonl",
        "premises_coqgym.jsonl"
    ]
    premises = merge_files_simple(premise_files)
    write_simple_jsonl(premises, joinpath(OUTPUT_DIR, "premises_merged.jsonl"))
    
    # Simple statistics
    stats = Dict{
        "version" => "v2.0-simple-merge",
        "merge_date" => string(Dates.now()),
        "total_proofs" => length(proof_states),
        "total_tactics" => length(tactics),
        "total_premises" => length(premises)
    }
    
    open(joinpath(OUTPUT_DIR, "stats_merged.json"), "w") do io
        JSON.write(io, stats)
    end
    
    println("\n🎉 Simple merge complete!")
    println("  Proofs: $(length(proof_states))")
    println("  Tactics: $(length(tactics))")
    println("  Premises: $(length(premises))")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end