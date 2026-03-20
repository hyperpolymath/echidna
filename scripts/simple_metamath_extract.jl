#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Simple Metamath proof extractor

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
    in_theorem = false
    
    for line in eachline(file_path)
        # Skip comments
        if startswith(line, raw"$") || startswith(line, raw"$)") || isempty(strip(line))
            continue
        end
        
        # Theorem declaration ($p)
        if startswith(line, raw"$p ")
            # Extract theorem name
            parts = split(line, "$p ")
            if length(parts) > 1
                name_part = split(parts[2], " ")[1]
                current_name = strip(name_part)
                current_statement = ""
                current_proof = ""
                in_theorem = true
            end
        
        # Statement ($e or $a)
        elseif in_theorem && (startswith(line, raw"$e ") || startswith(line, raw"$a "))
            statement = replace(line, r"^\$[ea]\s+" => s"")
            statement = replace(statement, raw" $" => s"")
            current_statement *= " " * strip(statement)
        
        # Proof start ($=)
        elseif in_theorem && occursin(raw"$=", line)
            proof_part = split(line, raw"$=")[2]
            current_proof = strip(proof_part)
            in_theorem = false
            
            # Save theorem
            if current_name != "" && current_proof != ""
                push!(theorems, Theorem(current_name, current_statement, current_proof))
                current_name = ""
                current_statement = ""
                current_proof = ""
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
            "source" => "Metamath"
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
        "version" => "v2.0-metamath-simple",
        "extraction_date" => Dates.now(),
        "total_proofs" => length(theorems),
        "total_tactics" => length(theorems),
        "source" => "Metamath set.mm (first 1000 theorems)",
        "prover" => "Metamath"
    )
    
    open("training_data/stats_metamath.json", "w") do io
        JSON3.pretty(io, stats)
    end
    
    println("✓ Extracted $(length(theorems)) theorems from Metamath")
    println("  Files saved: proof_states_metamath.jsonl, tactics_metamath.jsonl")
    
    return length(theorems)
end

# Main execution
if abspath(PROGRAM_FILE) == @__FILE__
    println("Simple Metamath Extractor")
    println("========================")
    
    file_path = "external_corpora/metamath/set.mm"
    
    if !isfile(file_path)
        error("File not found: $file_path")
    end
    
    println("\nExtracting from $file_path...")
    theorems = extract_theorems(file_path)
    println("Found $(length(theorems)) theorems")
    
    println("\nSaving training data...")
    save_as_training_data(theorems)
end
