#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs from Metamath set.mm for ECHIDNA training corpus

using JSON3
using Dates

struct MetamathProof
    theorem_name::String
    statement::String
    proof::String
    proof_length::Int
    proof_steps::Int
end

"""
Parse a Metamath proof string and count steps
"""
function parse_proof(proof_str::String)::Tuple{String, Int, Int}
    # Remove comments and whitespace
    clean_proof = replace(proof_str, r"\$\{.*?\}\$" => s"")
    clean_proof = replace(clean_proof, r"\$\\.*?\$" => s"")
    clean_proof = replace(clean_proof, r"\s+" => s" ")
    clean_proof = strip(clean_proof)
    
    # Count proof steps (compressed proof format)
    proof_steps = length(split(clean_proof, r"\s+"))
    proof_length = length(clean_proof)
    
    return (clean_proof, proof_length, proof_steps)
end

"""
Extract theorems from Metamath .mm file
"""
function extract_metamath_proofs(file_path::String)::Vector{MetamathProof}
    proofs = MetamathProof[]
    
    current_theorem = ""
    current_statement = ""
    current_proof = ""
    in_proof = false
    
    for line in eachline(file_path)
        # Skip comments and empty lines
        if startswith(line, '$') || isempty(strip(line))
            continue
        end
        
        # Theorem declaration
        if startswith(line, '$') && occursin(r"^\$\{.*?\}\$", line)
            # Extract theorem name
            theorem_match = match(r"^\$\{([^}]+)\}\$", line)
            if theorem_match !== nothing
                current_theorem = theorem_match.captures[1]
                current_statement = ""
                current_proof = ""
                in_proof = false
            end
        
        # Statement (between $a and $p)
        elseif occursin(r"^\$a\s+", line) || occursin(r"^\$e\s+", line)
            if current_theorem != ""
                statement_line = replace(line, r"^\$[ae]\s+" => s"")
                current_statement *= " " * statement_line
            end
        
        # Proof start
        elseif occursin(r"^\$p\s+", line)
            in_proof = true
            proof_line = replace(line, r"^\$p\s+" => s"")
            current_proof *= " " * proof_line
        
        # Proof continuation
        elseif in_proof && !isempty(strip(line))
            current_proof *= " " * strip(line)
        
        # Proof end (empty line or next theorem)
        elseif in_proof && (isempty(strip(line)) || startswith(strip(line), '$'))
            if current_theorem != "" && current_proof != ""
                clean_proof, proof_length, proof_steps = parse_proof(current_proof)
                
                push!(proofs, MetamathProof(
                    current_theorem,
                    current_statement,
                    clean_proof,
                    proof_length,
                    proof_steps
                ))
                
                current_theorem = ""
                current_statement = ""
                current_proof = ""
                in_proof = false
            end
        end
    end
    
    return proofs
end

"""
Convert Metamath proofs to ECHIDNA training format
"""
function convert_to_training_data(proofs::Vector{MetamathProof})::Vector{Dict}
    training_examples = Dict[]
    
    for (i, proof) in enumerate(proofs)
        # Create proof state
        proof_state = Dict(
            "id" => i,
            "prover" => "Metamath",
            "theorem" => proof.theorem_name,
            "goal" => proof.statement,
            "context" => String[],
            "proof_length" => proof.proof_length,
            "proof_steps" => proof.proof_steps
        )
        
        push!(training_examples, proof_state)
        
        # Create tactic sequence (Metamath proofs are single-step)
        tactic = Dict(
            "proof_id" => i,
            "step" => 1,
            "tactic" => "metamath_prove",
            "prover" => "Metamath",
            "proof_text" => proof.proof
        )
        
        push!(training_examples, tactic)
    end
    
    return training_examples
end

"""
Save training data to JSONL files
"""
function save_training_data(examples::Vector{Dict}, output_dir::String = "training_data")
    mkpath(output_dir)
    
    # Separate proof states and tactics
    proof_states = Dict[]
    tactics = Dict[]
    
    for example in examples
        if haskey(example, "goal")
            push!(proof_states, example)
        elseif haskey(example, "tactic")
            push!(tactics, example)
        end
    end
    
    # Save proof states
    open(joinpath(output_dir, "proof_states_metamath.jsonl"), "w") do io
        for state in proof_states
            println(io, JSON3.write(state))
        end
    end
    
    # Save tactics
    open(joinpath(output_dir, "tactics_metamath.jsonl"), "w") do io
        for tactic in tactics
            println(io, JSON3.write(tactic))
        end
    end
    
    # Save stats
    stats = Dict(
        "version" => "v2.0-metamath",
        "source" => "Metamath set.mm",
        "extraction_date" => Dates.now(),
        "total_proofs" => length(proof_states),
        "total_tactics" => length(tactics),
        "prover" => "Metamath"
    )
    
    open(joinpath(output_dir, "stats_metamath.json"), "w") do io
        JSON3.pretty(io, stats)
    end
    
    println("✓ Metamath extraction complete!")
    println("  Proofs extracted: $(length(proof_states))")
    println("  Tactics extracted: $(length(tactics))")
    println("  Files saved to: $output_dir")
    println("\nTo merge with main training data:")
    println("  cat proof_states_metamath.jsonl >> proof_states.jsonl")
    println("  cat tactics_metamath.jsonl >> tactics.jsonl")
    
    return (length(proof_states), length(tactics))
end

"""
Main extraction function
"""
function extract_metamath()
    println("Metamath Proof Extraction")
    println("=========================")
    
    file_path = "external_corpora/metamath/set.mm"
    
    if !isfile(file_path)
        error("Metamath set.mm not found at $file_path")
    end
    
    println("\nExtracting proofs from $file_path...")
    proofs = extract_metamath_proofs(file_path)
    println("  Found $(length(proofs)) theorems with proofs")
    
    println("\nConverting to training format...")
    examples = convert_to_training_data(proofs)
    
    println("\nSaving training data...")
    save_training_data(examples)
    
    return proofs
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    extract_metamath()
end
