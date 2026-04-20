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
    content = try
        read(file_path, String)
    catch
        return theorems
    end

    # Strip comments (Metamath `$( ... $)`, possibly nested).
    stripped = IOBuffer()
    depth = 0
    i = firstindex(content)
    lastidx = lastindex(content)
    while i <= lastidx
        if depth == 0 && i < lastidx && content[i] == '$' && content[nextind(content, i)] == '('
            depth += 1
            i = nextind(content, nextind(content, i))
        elseif depth > 0 && i < lastidx && content[i] == '$' && content[nextind(content, i)] == ')'
            depth -= 1
            i = nextind(content, nextind(content, i))
        elseif depth == 0
            print(stripped, content[i])
            i = nextind(content, i)
        else
            i = nextind(content, i)
        end
    end
    text = String(take!(stripped))

    # Match NAME $p STMT $= PROOF $.
    # Names are /[A-Za-z0-9_-]+/. Statement/proof bodies can span
    # lines; [^$]+ handles that since $ delimits everything in
    # Metamath syntax.
    pat = r"(\S+)\s+\$p\s+([^$]+?)\s+\$=\s*([^$]+?)\s*\$\."s
    for m in eachmatch(pat, text)
        name = strip(String(m.captures[1]))
        stmt = replace(strip(String(m.captures[2])), r"\s+" => " ")
        proof = replace(strip(String(m.captures[3])), r"\s+" => " ")
        (isempty(name) || isempty(proof)) && continue
        push!(theorems, Theorem(name, first(stmt, 1500), first(proof, 1500)))
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

    # Widening (2026-04-18): walk every .mm database in the Metamath
    # corpus, not just set.mm. The metamath/set.mm GitHub repo ships
    # multiple databases: set.mm (main, ~47K theorems), iset.mm
    # (intuitionistic, ~25K), nf.mm (New Foundations), hol.mm
    # (HOL-in-metamath), ql.mm (quantum logic), peano.mm,
    # big-unifier.mm, demo0.mm, miu.mm. Each adds orthogonal content.
    corpus_dir = "external_corpora/metamath"
    if !isdir(corpus_dir)
        println("Error: corpus directory not found: $(corpus_dir)")
        return 1
    end

    mm_files = String[]
    for f in readdir(corpus_dir; join=true)
        endswith(f, ".mm") && push!(mm_files, f)
    end
    println("Found $(length(mm_files)) .mm databases in $(corpus_dir)")

    all_theorems = Theorem[]
    for mm in mm_files
        println("\nExtracting from $(basename(mm))...")
        ts = extract_theorems(mm)
        println("  $(length(ts)) theorems")
        append!(all_theorems, ts)
    end

    println("\nTotal theorems across $(length(mm_files)) databases: $(length(all_theorems))")

    if !isempty(all_theorems)
        println("\nFirst few theorems:")
        for (i, theorem) in enumerate(first(all_theorems, 5))
            println("  $i. $(theorem.name)")
        end
    end

    println("\nSaving training data...")
    save_as_training_data(all_theorems)

    return 0
end

main()
