#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
COMPREHENSIVE VOCABULARY EXPANSION - Reach 1000+ words

Target: Expand vocabulary from 365 to 1000+ words
"""

import json
import os
from typing import List, Set

def extract_vocabulary_from_proofs():
    """Extract vocabulary from all existing proofs."""
    print("🔄 Extracting vocabulary from existing proofs...")
    
    # Read all proof files
    proof_files = [
        "training_data/proof_states_ABSOLUTE_COMPLETE.jsonl",
        "training_data/proof_states_ULTIMATE.jsonl",
        "training_data/proof_states_FINAL_BALANCED.jsonl",
        "training_data/proof_states_COMPLETE.jsonl"
    ]
    
    all_vocab = set()
    
    for filepath in proof_files:
        if os.path.exists(filepath):
            with open(filepath, 'r', encoding='utf-8') as f:
                for line in f:
                    try:
                        proof = json.loads(line.strip())
                        goal = proof.get('goal', '')
                        # Extract words from goal (simple approach)
                        words = goal.split()
                        for word in words:
                            # Basic cleaning
                            clean_word = word.strip('.,;:()[]{}!@#$%^&*').lower()
                            if len(clean_word) > 2 and clean_word.isalpha():
                                all_vocab.add(clean_word)
                    except:
                        continue
    
    print(f"✅ Extracted {len(all_vocab)} words from proof goals")
    return all_vocab

def add_mathematical_vocabulary():
    """Add comprehensive mathematical vocabulary."""
    print("🔄 Adding mathematical vocabulary...")
    
    math_vocab = {
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
    }
    
    print(f"✅ Added {len(math_vocab)} mathematical words")
    return math_vocab

def add_cs_vocabulary():
    """Add computer science vocabulary."""
    print("🔄 Adding computer science vocabulary...")
    
    cs_vocab = {
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
    }
    
    print(f"✅ Added {len(cs_vocab)} CS words")
    return cs_vocab

def add_specialized_vocabulary():
    """Add specialized domain vocabulary."""
    print("🔄 Adding specialized vocabulary...")
    
    specialized_vocab = {
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
    }
    
    print(f"✅ Added {len(specialized_vocab)} specialized words")
    return specialized_vocab

def add_synonyms_and_variants():
    """Add synonyms and word variants."""
    print("🔄 Adding synonyms and variants...")
    
    synonyms = {
        # Mathematical
        "eq": "equation", "eqn": "equation", "func": "function",
        "var": "variable", "param": "parameter", "const": "constant",
        
        # CS
        "alg": "algorithm", "impl": "implementation", "spec": "specification",
        "opt": "optimization", "approx": "approximation",
        
        # General
        "eg": "example", "ie": "that is", "etc": "et cetera",
        "wrt": "with respect to", "iff": "if and only if"
    }
    
    print(f"✅ Added {len(synonyms)} synonyms/variants")
    return synonyms

def main():
    """Main vocabulary expansion function."""
    
    print("🎯 COMPREHENSIVE VOCABULARY EXPANSION")
    print("=" * 50)
    print("Target: 1000+ vocabulary words")
    print("Current: ~365 words")
    print("Need: ~635 more words")
    
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
    
    # Combine all (convert dicts to sets first)
    all_vocab = proof_vocab.union(set(math_vocab.keys()), set(cs_vocab.keys()), set(specialized_vocab.keys()), set(synonym_vocab.keys()))
    
    print(f"\n✅ Total vocabulary collected: {len(all_vocab)} words")
    
    # Save comprehensive vocabulary
    output_file = "training_data/vocabulary_COMPREHENSIVE.txt"
    with open(output_file, 'w', encoding='utf-8') as f:
        for word in sorted(all_vocab):
            f.write(word + '\n')
    
    print(f"✅ Saved comprehensive vocabulary to {output_file}")
    
    # Update statistics
    stats = {
        "version": "v2.0-comprehensive",
        "date": "2026-03-20",
        "original_vocabulary": 365,
        "added_vocabulary": len(all_vocab) - 365,
        "total_vocabulary": len(all_vocab),
        "target_vocabulary": 1000,
        "status": "on track" if len(all_vocab) >= 1000 else "in progress"
    }
    
    with open("training_data/stats_COMPREHENSIVE.json", 'w', encoding='utf-8') as f:
        json.dump(stats, f, indent=2)
    
    print(f"\n✅ Statistics saved to training_data/stats_COMPREHENSIVE.json")
    
    if len(all_vocab) >= 1000:
        print("\n🎉 VOCABULARY TARGET ACHIEVED!")
        print(f"   Reached {len(all_vocab)} words (target: 1000)")
    else:
        remaining = 1000 - len(all_vocab)
        print(f"\n⚠️  VOCABULARY TARGET IN PROGRESS")
        print(f"   Current: {len(all_vocab)} words")
        print(f"   Remaining: {remaining} words needed")
        print(f"   Status: {len(all_vocab)/1000*100:.1f}% complete")

if __name__ == "__main__":
    main()