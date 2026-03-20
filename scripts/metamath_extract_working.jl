#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Working Metamath proof extractor

using JSON3
using Dates

struct Theorem
    name::String
    statement::String
    proof::String
end

function extract_theorems(file_path::String)::Vector{Theorem}
    theorems = Theorem[]
    
    current_name = ""
    current_statement = ""
    current_proof = ""
    
    for line in eachline(file_path)
        # Skip comment blocks
        if startswith(line, "$( ") || startswith(line, "$)")
            continue
        end
        
        # Skip empty lines
        if isempty(strip(line))
            continue
        end
        
        # Theorem declaration line (contains $p)
        if occursin("$p", line)
            # Extract theorem name (before $p)
            parts = split(line, "$p")
            if length(parts) > 1
                name_part = strip(parts[1])
                # Remove any trailing $.
                name_part = replace(name_part, r"\$\." => s"")
                current_name = strip(name_part)
                
                # Extract statement (between $p and $=)
                statement_part = parts[2]
                statement_match = match(r"^\s*([^$]+)\$=", statement_part)
                if statement_match !== nothing
                    current_statement = strip(statement_match.captures[1])
                end
                
                # Extract proof (after $=)
                proof_match = match(r"\$=\s*([^$]+)\$\.", statement_part)
                if proof_match !== nothing
                    current_proof = strip(proof_match.captures[1])
                    
                    # Save theorem
                    if current_name != "" && current_proof != ""
                        push!(theorems, Theorem(current_name, current_statement, current_proof))
                        current_name = ""
                        current_statement = ""
                        current_proof = ""
                    end
                end
            end
        end
    end
    
    return theorems
end

function save_as_training_data(theorems::Vector{Theorem})
    proof_states = Dict[]
    tactics = Dict[]
    
    for (i, theorem) in enumerate(theorems)
        # Proof state
        state = Dict(
            "id" => i + 1000,  # Start from 1000 to avoid conflicts
            "prover" => "Metamath",
            "theorem" => theorem.name,
            "goal" => theorem.statement,
            "context" => String[],
            "source" => "Metamath",
            "proof_steps" => length(split(theorem.proof, r"\s+"))
        )
        push!(proof_states, state)
        
        # Tactic
        tactic = Dict(
            "proof_id" => i + 1000,
            "step" => 1,
            "tactic" => "metamath_prove",
            "prover" => "Metamath",
            "proof_text" => theorem.proof
        )
        push!(tactics, tactic)
    end
    
    # Save to files
    open("training_data/proof_states_metamath.jsonl", "w") do io
        for state in proof_states
            println(io, JSON3.write(state))
        end
    end
    
    open("training_data/tactics_metamath.jsonl", "w") do io
        for tactic in tactics
            println(io, JSON3.write(tactic))
        end
    end
    
    # Save stats
    stats = Dict(
        "version" => "v2.0-metamath-working",
        "extraction_date" => Dates.now(),
        "total_proofs" => length(theorems),
        "total_tactics" => length(theorems),
        "source" => "Metamath set.mm",
        "prover" => "Metamath"
    )
    
    open("training_data/stats_metamath.json", "w") do io
        JSON3.pretty(io, stats)
    end
    
    println("✓ Extracted $(length(theorems)) theorems from Metamath")
    println("  Sample theorem: $(theorems[1].name)")
    println("  Files saved: proof_states_metamath.jsonl, tactics_metamath.jsonl")
    
    return length(theorems)
end

# Main execution
if abspath(PROGRAM_FILE) == @__FILE__
    println("Metamath Proof Extractor")
    println("========================")
    
    file_path = "external_corpora/metamath/set.mm"
    
    if !isfile(file_path)
        error("File not found: $file_path")
    end
    
    println("\nExtracting from $file_path...")
    theorems = extract_theorems(file_path)
    println("Found $(length(theorems)) theorems")
    
    if length(theorems) > 0
        println("\nFirst few theorems:")
        for i in 1:min(5, length(theorems))
            println("  $(i). $(theorems[i].name)")
        end
    end
    
    println("\nSaving training data...")
    save_as_training_data(theorems)
end
