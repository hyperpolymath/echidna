#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from CoqGym corpus and convert to ECHIDNA training format.

CoqGym contains high-quality Coq proofs that will improve our corpus diversity.
"""

import json
import os
import re
from pathlib import Path
from typing import Dict, List, Any

# Configuration
COQGYM_DIR = "external_corpora/CoqGym"
OUTPUT_DIR = "training_data"
PROOF_STATES_FILE = f"{OUTPUT_DIR}/proof_states_coqgym.jsonl"
TACTICS_FILE = f"{OUTPUT_DIR}/tactics_coqgym.jsonl"
PREMISES_FILE = f"{OUTPUT_DIR}/premises_coqgym.jsonl"
STATS_FILE = f"{OUTPUT_DIR}/stats_coqgym.json"

# Start ID after existing data (Metamath ended at 47165 + original 108 = 47273)
START_ID = 47274

def extract_coqgym_proofs() -> tuple[List[Dict[str, Any]], List[Dict[str, Any]], List[Dict[str, Any]]]:
    """Extract proofs from CoqGym corpus."""
    
    proof_states = []
    tactics = []
    premises = []
    current_id = START_ID
    
    # Look for CoqGym proof files
    coqgym_proofs_dir = os.path.join(COQGYM_DIR, "coq_projects")
    
    if not os.path.exists(coqgym_proofs_dir):
        print(f"❌ CoqGym proofs directory not found: {coqgym_proofs_dir}")
        return [], [], []
    
    # Find .v files (Coq source files)
    v_files = []
    for root, dirs, files in os.walk(coqgym_proofs_dir):
        for file in files:
            if file.endswith('.v'):
                v_files.append(os.path.join(root, file))
    
    print(f"🔍 Found {len(v_files)} Coq files in CoqGym")
    
    # Simple extraction - look for theorems and proofs
    theorem_pattern = r'Theorem\s+([a-zA-Z0-9_]+)\s*:\s*(.*?)\s*\.'
    proof_pattern = r'Proof\.(.*?)\Q.'
    tactic_pattern = r'\.\s*([a-zA-Z0-9_]+)'
    
    for v_file in v_files[:100]:  # Limit to first 100 files for now
        try:
            with open(v_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Extract theorems
            for theorem_match in re.finditer(theorem_pattern, content, re.DOTALL):
                theorem_name = theorem_match.group(1).strip()
                theorem_statement = theorem_match.group(2).strip()
                
                if theorem_name and theorem_statement:
                    # Create proof state
                    proof_state = {
                        "id": current_id,
                        "prover": "Coq",
                        "theorem": theorem_name,
                        "goal": theorem_statement,
                        "context": []
                    }
                    proof_states.append(proof_state)
                    
                    # Look for proof and extract tactics
                    proof_start = theorem_match.end()
                    remaining_content = content[proof_start:]
                    proof_match = re.search(proof_pattern, remaining_content, re.DOTALL)
                    
                    if proof_match:
                        proof_content = proof_match.group(1)
                        
                        # Extract tactics (simplified)
                        for step, tactic_match in enumerate(re.finditer(tactic_pattern, proof_content)):
                            tactic = tactic_match.group(1).strip()
                            
                            if tactic:
                                tactics.append({
                                    "proof_id": current_id,
                                    "step": step + 1,
                                    "tactic": tactic,
                                    "prover": "Coq"
                                })
                        
                        # Extract premises (hypotheses)
                        hyp_pattern = r'intros?\s+([a-zA-Z0-9_\s]+)'
                        for hyp_match in re.finditer(hyp_pattern, proof_content):
                            hyps = hyp_match.group(1).strip().split()
                            for hyp in hyps:
                                premises.append({
                                    "proof_id": current_id,
                                    "premise": hyp,
                                    "prover": "Coq",
                                    "theorem": theorem_name
                                })
                    
                    current_id += 1
                    
        except Exception as e:
            print(f"⚠️  Error processing {v_file}: {e}")
    
    return proof_states, tactics, premises

def save_extracted_data(proof_states: List[Dict[str, Any]], 
                       tactics: List[Dict[str, Any]], 
                       premises: List[Dict[str, Any]]):
    """Save extracted data to JSONL files."""
    
    # Create output directory
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    
    # Save proof states
    with open(PROOF_STATES_FILE, 'w', encoding='utf-8') as f:
        for state in proof_states:
            f.write(json.dumps(state, ensure_ascii=False) + '\n')
    
    # Save tactics
    with open(TACTICS_FILE, 'w', encoding='utf-8') as f:
        for tactic in tactics:
            f.write(json.dumps(tactic, ensure_ascii=False) + '\n')
    
    # Save premises
    with open(PREMISES_FILE, 'w', encoding='utf-8') as f:
        for premise in premises:
            f.write(json.dumps(premise, ensure_ascii=False) + '\n')
    
    # Save statistics
    stats = {
        "source": "CoqGym",
        "extraction_date": "2026-03-20",
        "proof_states_count": len(proof_states),
        "tactics_count": len(tactics),
        "premises_count": len(premises),
        "start_id": START_ID,
        "end_id": START_ID + len(proof_states) - 1 if proof_states else START_ID
    }
    
    with open(STATS_FILE, 'w', encoding='utf-8') as f:
        json.dump(stats, f, indent=2)
    
    print(f"✅ Saved {len(proof_states)} proof states to {PROOF_STATES_FILE}")
    print(f"✅ Saved {len(tactics)} tactics to {TACTICS_FILE}")
    print(f"✅ Saved {len(premises)} premises to {PREMISES_FILE}")
    print(f"✅ Saved statistics to {STATS_FILE}")

def merge_with_existing_data():
    """Merge CoqGym data with existing training data."""
    
    print("🔄 Merging CoqGym data with existing corpus...")
    
    # This would combine the new data with existing files
    # For now, we'll just create separate files that can be merged later
    
    print("✅ CoqGym data extraction complete!")
    print("📝 To merge with main corpus, run:")
    print("   julia scripts/merge_training_data.jl")

def main():
    """Main extraction function."""
    
    print("🚀 ECHIDNA CoqGym Extraction")
    print("=" * 40)
    
    # Extract proofs from CoqGym
    proof_states, tactics, premises = extract_coqgym_proofs()
    
    if not proof_states:
        print("❌ No proofs extracted from CoqGym")
        return
    
    # Save extracted data
    save_extracted_data(proof_states, tactics, premises)
    
    # Merge with existing data
    merge_with_existing_data()
    
    print(f"\n🎉 Extraction Summary:")
    print(f"   Proofs: {len(proof_states)}")
    print(f"   Tactics: {len(tactics)}")
    print(f"   Premises: {len(premises)}")
    print(f"   ID Range: {START_ID} - {START_ID + len(proof_states) - 1}")

if __name__ == "__main__":
    main()