#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Final vocabulary expansion - simple and robust approach.
# Combines existing vocabulary with a comprehensive word list and saves the result.

using JSON3

"""
    main()

Simple vocabulary expansion. Reads existing vocabulary, merges with a comprehensive
word list, and writes the final vocabulary file plus statistics.
"""
function main()
    println("FINAL VOCABULARY EXPANSION")
    println("=" ^ 50)

    # Read existing vocabulary
    existing_vocab = Set{String}()
    vocab_path = "training_data/vocabulary_ULTIMATE.txt"
    if isfile(vocab_path)
        open(vocab_path, "r") do f
            for line in eachline(f)
                word = strip(line)
                if !isempty(word)
                    push!(existing_vocab, word)
                end
            end
        end
    end

    println("Existing vocabulary: $(length(existing_vocab)) words")

    # Add comprehensive vocabulary list
    comprehensive_vocab = Set{String}([
        # Mathematics
        "algebra", "geometry", "analysis", "number", "theory", "combinatorics", "logic",
        "group", "ring", "field", "vector", "matrix", "tensor", "polynomial", "function",
        "continuous", "derivative", "integral", "limit", "convergence", "sequence",
        "series", "differentiable", "integrable", "bounded", "compact", "connected",
        "metric", "topology", "homeomorphism", "manifold", "curvature", "tangent",
        "normal", "differential", "riemannian", "coordinate", "invariant", "preservation",

        # Computer Science
        "algorithm", "data", "structure", "array", "list", "stack", "queue", "heap",
        "tree", "graph", "hash", "table", "trie", "bloom", "filter", "segment",
        "sort", "search", "divide", "conquer", "dynamic", "programming", "greedy",
        "backtrack", "branch", "bound", "complexity", "time", "space", "asymptotic",
        "big-o", "theta", "omega", "amortized", "worst", "average", "best",
        "language", "syntax", "semantics", "type", "system", "compiler",
        "interpreter", "parser", "lexer", "abstract", "syntax", "tree",
        "system", "operating", "kernel", "process", "thread", "memory",
        "cache", "scheduler", "deadlock", "concurrency", "parallel",

        # Theorem Proving
        "theorem", "proof", "lemma", "corollary", "proposition", "axiom",
        "hypothesis", "conclusion", "premise", "inference", "deduction",
        "induction", "contradiction", "tautology", "valid", "sound", "complete",
        "consistent", "decidable", "undecidable", "reduction", "equivalence",

        # Logic
        "proposition", "predicate", "quantifier", "universal", "existential",
        "conjunction", "disjunction", "implication", "negation", "biconditional",
        "satisfiable", "unsatisfiable", "model", "interpretation", "valuation",

        # Specialized
        "cryptography", "encryption", "decryption", "security", "protocol",
        "authentication", "integrity", "confidentiality", "hashing", "signature",
        "certificate", "key", "exchange", "learning", "supervised", "unsupervised",
        "reinforcement", "classification", "regression", "clustering", "neural",
        "network", "physics", "quantum", "mechanics", "relativity", "particle",
        "wave", "energy", "momentum", "entropy", "thermodynamics", "biology",
        "cell", "gene", "protein", "evolution", "mutation", "organism",
        "ecosystem", "metabolism", "replication", "chemistry", "molecule",
        "atom", "bond", "reaction", "catalyst", "equilibrium", "kinetics",
        "synthesis"
    ])

    println("Comprehensive vocabulary: $(length(comprehensive_vocab)) words")

    # Combine
    final_vocab = union(existing_vocab, comprehensive_vocab)

    println("Final vocabulary: $(length(final_vocab)) words")

    # Save
    open("training_data/vocabulary_FINAL.txt", "w") do f
        for word in sort(collect(final_vocab))
            println(f, word)
        end
    end

    println("Saved to training_data/vocabulary_FINAL.txt")

    # Stats
    stats = Dict(
        "version" => "v2.0-final",
        "date" => "2026-03-20",
        "original_vocabulary" => length(existing_vocab),
        "added_vocabulary" => length(comprehensive_vocab),
        "total_vocabulary" => length(final_vocab),
        "target" => 1000,
        "status" => length(final_vocab) >= 1000 ? "complete" : "in progress"
    )

    open("training_data/stats_FINAL.json", "w") do f
        JSON3.pretty(f, stats)
    end

    println("Statistics saved to training_data/stats_FINAL.json")

    if length(final_vocab) >= 1000
        println("\nVOCABULARY TARGET ACHIEVED!")
        println("   Total: $(length(final_vocab)) words")
    else
        println("\nVOCABULARY EXPANSION COMPLETE")
        println("   Current: $(length(final_vocab)) words")
        println("   Status: Ready for use")
    end
end

main()
