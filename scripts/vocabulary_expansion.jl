#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Comprehensive vocabulary expansion - reach 1000+ words.
# Extracts vocabulary from existing proofs and adds domain-specific word lists
# for mathematics, computer science, and specialized fields.

using JSON3

"""
    extract_vocabulary_from_proofs() -> Set{String}

Extract vocabulary words from all existing proof goal fields.
"""
function extract_vocabulary_from_proofs()::Set{String}
    println("Extracting vocabulary from existing proofs...")

    # Read all proof files
    proof_files = [
        "training_data/proof_states_ABSOLUTE_COMPLETE.jsonl",
        "training_data/proof_states_ULTIMATE.jsonl",
        "training_data/proof_states_FINAL_BALANCED.jsonl",
        "training_data/proof_states_COMPLETE.jsonl"
    ]

    all_vocab = Set{String}()

    for filepath in proof_files
        if isfile(filepath)
            open(filepath, "r") do f
                for line in eachline(f)
                    try
                        proof = JSON3.read(line, Dict{String,Any})
                        goal = get(proof, "goal", "")
                        # Extract words from goal (simple approach)
                        words = split(goal)
                        for word in words
                            # Basic cleaning
                            clean_word = lowercase(strip(word, ['.', ',', ';', ':', '(', ')', '[', ']', '{', '}', '!', '@', '#', '$', '%', '^', '&', '*']))
                            if length(clean_word) > 2 && all(isletter, clean_word)
                                push!(all_vocab, clean_word)
                            end
                        end
                    catch
                        continue
                    end
                end
            end
        end
    end

    println("Extracted $(length(all_vocab)) words from proof goals")
    return all_vocab
end

"""
    add_mathematical_vocabulary() -> Set{String}

Return a set of comprehensive mathematical vocabulary words.
"""
function add_mathematical_vocabulary()::Set{String}
    println("Adding mathematical vocabulary...")

    math_vocab = Set{String}([
        # Algebra
        "algebra", "group", "ring", "field", "homomorphism", "isomorphism",
        "subgroup", "coset", "ideal", "quotient", "polynomial", "monomial",
        "coefficient", "root", "factor", "irreducible", "gcd", "lcm",

        # Analysis
        "analysis", "limit", "continuity", "derivative", "integral", "convergence",
        "sequence", "series", "differentiable", "integrable", "bounded",
        "compact", "connected", "metric", "topology", "homeomorphism",

        # Geometry
        "geometry", "euclidean", "manifold", "curvature", "tangent", "normal",
        "differential", "riemannian", "vector", "tensor", "coordinate",

        # Number Theory
        "number", "prime", "composite", "divisor", "modular", "congruence",
        "residue", "quadratic", "reciprocity", "diophantine", "fermat",

        # Combinatorics
        "combinatorics", "permutation", "combination", "partition", "graph",
        "tree", "path", "cycle", "clique", "matching", "chromatic",

        # Logic
        "logic", "proposition", "predicate", "quantifier", "tautology",
        "contradiction", "satisfiable", "valid", "sound", "complete"
    ])

    println("Added $(length(math_vocab)) mathematical words")
    return math_vocab
end

"""
    add_cs_vocabulary() -> Set{String}

Return a set of computer science vocabulary words.
"""
function add_cs_vocabulary()::Set{String}
    println("Adding computer science vocabulary...")

    cs_vocab = Set{String}([
        # Data Structures
        "array", "list", "stack", "queue", "heap", "tree", "graph",
        "hash", "table", "trie", "bloom", "filter", "segment",

        # Algorithms
        "algorithm", "sort", "search", "divide", "conquer", "dynamic",
        "programming", "greedy", "backtrack", "branch", "bound",

        # Complexity
        "complexity", "time", "space", "asymptotic", "big-o", "theta",
        "omega", "amortized", "worst", "average", "best",

        # Programming Languages
        "language", "syntax", "semantics", "type", "system", "compiler",
        "interpreter", "parser", "lexer", "abstract", "syntax", "tree",

        # Systems
        "system", "operating", "kernel", "process", "thread", "memory",
        "cache", "scheduler", "deadlock", "concurrency", "parallel"
    ])

    println("Added $(length(cs_vocab)) CS words")
    return cs_vocab
end

"""
    add_specialized_vocabulary() -> Set{String}

Return a set of specialized domain vocabulary words.
"""
function add_specialized_vocabulary()::Set{String}
    println("Adding specialized vocabulary...")

    specialized_vocab = Set{String}([
        # Cryptography
        "cryptography", "encryption", "decryption", "cipher", "protocol",
        "security", "authentication", "integrity", "confidentiality",
        "hashing", "signature", "certificate", "key", "exchange",

        # Machine Learning
        "learning", "supervised", "unsupervised", "reinforcement",
        "classification", "regression", "clustering", "neural", "network",

        # Physics
        "physics", "quantum", "mechanics", "relativity", "particle",
        "wave", "energy", "momentum", "entropy", "thermodynamics",

        # Biology
        "biology", "cell", "gene", "protein", "evolution", "mutation",
        "organism", "ecosystem", "metabolism", "replication",

        # Chemistry
        "chemistry", "molecule", "atom", "bond", "reaction", "catalyst",
        "equilibrium", "thermodynamics", "kinetics", "synthesis"
    ])

    println("Added $(length(specialized_vocab)) specialized words")
    return specialized_vocab
end

"""
    add_synonyms_and_variants() -> Dict{String,String}

Return a dictionary mapping abbreviations to their full forms.
"""
function add_synonyms_and_variants()::Dict{String,String}
    println("Adding synonyms and variants...")

    synonyms = Dict{String,String}(
        # Mathematical
        "eq" => "equation", "eqn" => "equation", "func" => "function",
        "var" => "variable", "param" => "parameter", "const" => "constant",

        # CS
        "alg" => "algorithm", "impl" => "implementation", "spec" => "specification",
        "opt" => "optimization", "approx" => "approximation",

        # General
        "eg" => "example", "ie" => "that is", "etc" => "et cetera",
        "wrt" => "with respect to", "iff" => "if and only if"
    )

    println("Added $(length(synonyms)) synonyms/variants")
    return synonyms
end

"""
    main()

Main vocabulary expansion function. Collects words from proofs and curated
domain lists, then saves the combined vocabulary and statistics.
"""
function main()
    println("COMPREHENSIVE VOCABULARY EXPANSION")
    println("=" ^ 50)
    println("Target: 1000+ vocabulary words")
    println("Current: ~365 words")
    println("Need: ~635 more words")

    # Step 1: Extract from existing proofs
    proof_vocab = extract_vocabulary_from_proofs()

    # Step 2: Add mathematical vocabulary
    math_vocab = add_mathematical_vocabulary()

    # Step 3: Add CS vocabulary
    cs_vocab = add_cs_vocabulary()

    # Step 4: Add specialized vocabulary
    specialized_vocab = add_specialized_vocabulary()

    # Step 5: Add synonyms
    synonym_vocab = add_synonyms_and_variants()

    # Combine all (convert dict keys to set)
    all_vocab = union(proof_vocab, math_vocab, cs_vocab, specialized_vocab, Set(keys(synonym_vocab)))

    println("\nTotal vocabulary collected: $(length(all_vocab)) words")

    # Save comprehensive vocabulary
    output_file = "training_data/vocabulary_COMPREHENSIVE.txt"
    open(output_file, "w") do f
        for word in sort(collect(all_vocab))
            println(f, word)
        end
    end

    println("Saved comprehensive vocabulary to $output_file")

    # Update statistics
    stats = Dict{String,Any}(
        "version" => "v2.0-comprehensive",
        "date" => "2026-03-20",
        "original_vocabulary" => 365,
        "added_vocabulary" => length(all_vocab) - 365,
        "total_vocabulary" => length(all_vocab),
        "target_vocabulary" => 1000,
        "status" => length(all_vocab) >= 1000 ? "on track" : "in progress"
    )

    open("training_data/stats_COMPREHENSIVE.json", "w") do f
        JSON3.pretty(f, stats)
    end

    println("\nStatistics saved to training_data/stats_COMPREHENSIVE.json")

    if length(all_vocab) >= 1000
        println("\nVOCABULARY TARGET ACHIEVED!")
        println("   Reached $(length(all_vocab)) words (target: 1000)")
    else
        remaining = 1000 - length(all_vocab)
        println("\nVOCABULARY TARGET IN PROGRESS")
        println("   Current: $(length(all_vocab)) words")
        println("   Remaining: $remaining words needed")
        pct = round(length(all_vocab) / 1000 * 100; digits=1)
        println("   Status: $(pct)% complete")
    end
end

main()
