#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
FINAL COMPLETE MERGE - Ensure ALL data is included
"""

import json
import os
from collections import defaultdict

def read_jsonl_file(filepath):
    """Read JSONL file and return list of dicts."""
    data = []
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        data.append(json.loads(line))
                    except json.JSONDecodeError:
                        continue
    except FileNotFoundError:
        pass
    return data

def merge_all_proof_data():
    """Merge all proof data files."""
    
    print("🔄 Merging ALL proof data...")
    
    # Find all proof state files
    files = [
        "training_data/proof_states.jsonl",
        "training_data/proof_states_v2.jsonl",
        "training_data/proof_states_2026-03-20.jsonl",
        "training_data/proof_states_metamath.jsonl",
        "training_data/proof_states_coqgym.jsonl",
        "training_data/proof_states_mathlib4.jsonl",
        "training_data/proof_states_coqgym_max.jsonl",
        "training_data/proof_states_mathlib4_max.jsonl",
    ]
    
    all_proofs = []
    seen_ids = set()
    
    for filepath in files:
        if os.path.exists(filepath):
            print(f"  Reading {filepath}...")
            proofs = read_jsonl_file(filepath)
            print(f"    Found {len(proofs)} proofs")
            
            # Deduplicate by ID
            for proof in proofs:
                if 'id' in proof and proof['id'] not in seen_ids:
                    all_proofs.append(proof)
                    seen_ids.add(proof['id'])
                elif 'id' not in proof:
                    # Generate new ID if missing
                    new_id = max(seen_ids) + 1 if seen_ids else 1
                    proof['id'] = new_id
                    all_proofs.append(proof)
                    seen_ids.add(new_id)
    
    print(f"  Total unique proofs: {len(all_proofs)}")
    print(f"  ID range: {min(p['id'] for p in all_proofs)} - {max(p['id'] for p in all_proofs)}")
    
    # Sort by ID
    all_proofs.sort(key=lambda x: x['id'])
    
    # Save
    with open("training_data/proof_states_COMPLETE.jsonl", 'w', encoding='utf-8') as f:
        for proof in all_proofs:
            f.write(json.dumps(proof, ensure_ascii=False) + '\n')
    
    return len(all_proofs)

def merge_all_tactics_data():
    """Merge all tactics data files."""
    
    print("🔄 Merging ALL tactics data...")
    
    # Find all tactics files
    files = [
        "training_data/tactics.jsonl",
        "training_data/tactics_v2.jsonl",
        "training_data/tactics_2026-03-20.jsonl",
        "training_data/tactics_metamath.jsonl",
        "training_data/tactics_coqgym.jsonl",
        "training_data/tactics_mathlib4.jsonl",
        "training_data/tactics_coqgym_max.jsonl",
        "training_data/tactics_mathlib4_max.jsonl",
    ]
    
    all_tactics = []
    
    for filepath in files:
        if os.path.exists(filepath):
            print(f"  Reading {filepath}...")
            tactics = read_jsonl_file(filepath)
            print(f"    Found {len(tactics)} tactics")
            all_tactics.extend(tactics)
    
    print(f"  Total tactics: {len(all_tactics)}")
    
    # Save
    with open("training_data/tactics_COMPLETE.jsonl", 'w', encoding='utf-8') as f:
        for tactic in all_tactics:
            f.write(json.dumps(tactic, ensure_ascii=False) + '\n')
    
    return len(all_tactics)

def merge_all_premises_data():
    """Merge all premises data files."""
    
    print("🔄 Merging ALL premises data...")
    
    # Find all premises files
    files = [
        "training_data/premises.jsonl",
        "training_data/premises_2026-03-20.jsonl",
        "training_data/premises_coqgym.jsonl",
        "training_data/premises_coqgym_max.jsonl",
    ]
    
    all_premises = []
    
    for filepath in files:
        if os.path.exists(filepath):
            print(f"  Reading {filepath}...")
            premises = read_jsonl_file(filepath)
            print(f"    Found {len(premises)} premises")
            all_premises.extend(premises)
    
    print(f"  Total premises: {len(all_premises)}")
    
    # Save
    with open("training_data/premises_COMPLETE.jsonl", 'w', encoding='utf-8') as f:
        for premise in all_premises:
            f.write(json.dumps(premise, ensure_ascii=False) + '\n')
    
    return len(all_premises)

def calculate_final_stats():
    """Calculate and save final statistics."""
    
    print("📊 Calculating final statistics...")
    
    # Read the complete files
    proofs = read_jsonl_file("training_data/proof_states_COMPLETE.jsonl")
    tactics = read_jsonl_file("training_data/tactics_COMPLETE.jsonl")
    premises = read_jsonl_file("training_data/premises_COMPLETE.jsonl")
    
    # Count by prover
    prover_counts = defaultdict(int)
    for proof in proofs:
        prover = proof.get('prover', 'unknown')
        prover_counts[prover] += 1
    
    tactic_prover_counts = defaultdict(int)
    for tactic in tactics:
        prover = tactic.get('prover', 'unknown')
        tactic_prover_counts[prover] += 1
    
    # Unique theorems
    theorems = set()
    for proof in proofs:
        theorem = proof.get('theorem', '')
        if theorem:
            theorems.add(theorem)
    
    # Unique tactics
    tactic_names = set()
    for tactic in tactics:
        tactic_name = tactic.get('tactic', '')
        if tactic_name:
            tactic_names.add(tactic_name)
    
    stats = {
        "version": "v2.0-COMPLETE",
        "merge_date": "2026-03-20",
        "total_proofs": len(proofs),
        "total_tactics": len(tactics),
        "total_premises": len(premises),
        "unique_theorems": len(theorems),
        "unique_tactics": len(tactic_names),
        "proofs_by_prover": dict(prover_counts),
        "tactics_by_prover": dict(tactic_prover_counts),
        "id_range": {
            "min": min(p['id'] for p in proofs if 'id' in p),
            "max": max(p['id'] for p in proofs if 'id' in p)
        },
        "sources": [
            "Original ECHIDNA corpus",
            "Metamath extraction",
            "CoqGym extraction (basic)",
            "CoqGym extraction (comprehensive)",
            "mathlib4 extraction (basic)",
            "mathlib4 extraction (comprehensive)"
        ]
    }
    
    with open("training_data/stats_COMPLETE.json", 'w', encoding='utf-8') as f:
        json.dump(stats, f, indent=2)
    
    print(f"  Total proofs: {len(proofs)}")
    print(f"  Total tactics: {len(tactics)}")
    print(f"  Total premises: {len(premises)}")
    print(f"  Unique theorems: {len(theorems)}")
    print(f"  Unique tactics: {len(tactic_names)}")
    print(f"  Provers: {len(prover_counts)}")
    
    return stats

def main():
    """Main merge function."""
    
    print("🚀 FINAL COMPLETE MERGE")
    print("=" * 50)
    
    # Merge all data
    proof_count = merge_all_proof_data()
    tactic_count = merge_all_tactics_data()
    premise_count = merge_all_premises_data()
    
    # Calculate statistics
    stats = calculate_final_stats()
    
    print(f"\n🎉 COMPLETE MERGE FINISHED!")
    print(f"   Proofs: {proof_count}")
    print(f"   Tactics: {tactic_count}")
    print(f"   Premises: {premise_count}")
    print(f"   Unique Theorems: {stats['unique_theorems']}")
    print(f"   Unique Tactics: {stats['unique_tactics']}")
    print(f"   Provers: {len(stats['proofs_by_prover'])}")
    
    print(f"\n📁 Files created:")
    print(f"   training_data/proof_states_COMPLETE.jsonl")
    print(f"   training_data/tactics_COMPLETE.jsonl")
    print(f"   training_data/premises_COMPLETE.jsonl")
    print(f"   training_data/stats_COMPLETE.json")

if __name__ == "__main__":
    main()