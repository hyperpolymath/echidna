#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from Lean mathlib4 corpus and convert to ECHIDNA training format.

mathlib4 contains high-quality Lean proofs that will improve our corpus diversity.
"""

import json
import os
import re
from pathlib import Path
from typing import Dict, List, Any

# Configuration
MATHLIB4_DIR = "external_corpora/mathlib4"
OUTPUT_DIR = "training_data"
PROOF_STATES_FILE = f"{OUTPUT_DIR}/proof_states_mathlib4.jsonl"
TACTICS_FILE = f"{OUTPUT_DIR}/tactics_mathlib4.jsonl"
PREMISES_FILE = f"{OUTPUT_DIR}/premises_mathlib4.jsonl"
STATS_FILE = f"{OUTPUT_DIR}/stats_mathlib4.json"

# Start ID after CoqGym (47274 + 14 = 47288)
START_ID = 47288

def extract_mathlib4_proofs() -> tuple[List[Dict[str, Any]], List[Dict[str, Any]], List[Dict[str, Any]]]:
    """Extract proofs from mathlib4 corpus."""
    
    proof_states = []
    tactics = []
    premises = []
    current_id = START_ID
    
    # Look for mathlib4 proof files
    mathlib4_proofs_dir = os.path.join(MATHLIB4_DIR, "Mathlib")
    
    if not os.path.exists(mathlib4_proofs_dir):
        print(f"❌ mathlib4 proofs directory not found: {mathlib4_proofs_dir}")
        return [], [], []
    
    # Find .lean files
    lean_files = []
    for root, dirs, files in os.walk(mathlib4_proofs_dir):
        for file in files:
            if file.endswith('.lean'):
                lean_files.append(os.path.join(root, file))
    
    print(f"🔍 Found {len(lean_files)} Lean files in mathlib4")
    
    # Simple extraction - look for theorems and proofs
    theorem_pattern = r'theorem\s+([a-zA-Z0-9_]+)\s*(.*?)\s*:=\s*by'
    lemma_pattern = r'lemma\s+([a-zA-Z0-9_]+)\s*(.*?)\s*:=\s*by'
    
    for lean_file in lean_files[:50]:  # Limit to first 50 files for now
        try:
            with open(lean_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Extract theorems and lemmas
            for pattern, proof_type in [(theorem_pattern, "theorem"), (lemma_pattern, "lemma")]:
                for match in re.finditer(pattern, content, re.DOTALL):
                    name = match.group(1).strip()
                    statement = match.group(2).strip()
                    
                    if name and statement:
                        # Create proof state
                        proof_state = {
                            "id": current_id,
                            "prover": "Lean",
                            "theorem": name,
                            "goal": statement,
                            "context": []
                        }
                        proof_states.append(proof_state)
                        
                        # Look for proof tactics (simplified)
                        proof_start = match.end()
                        remaining_content = content[proof_start:]
                        
                        # Extract tactics from the "by" clause
                        by_pattern = r'by\s+([^\n]+)'
                        by_match = re.search(by_pattern, remaining_content)
                        
                        if by_match:
                            tactics_str = by_match.group(1).strip()
                            # Split by tactic separators
                            individual_tactics = re.split(r'[\s,]+', tactics_str)
                            
                            for step, tactic in enumerate(individual_tactics):
                                if tactic:
                                    tactics.append({
                                        "proof_id": current_id,
                                        "step": step + 1,
                                        "tactic": tactic,
                                        "prover": "Lean"
                                    })
                        
                        current_id += 1
                        
        except Exception as e:
            print(f"⚠️  Error processing {lean_file}: {e}")
    
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
        "source": "mathlib4",
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

def main():
    """Main extraction function."""
    
    print("🚀 ECHIDNA mathlib4 Extraction")
    print("=" * 40)
    
    # Extract proofs from mathlib4
    proof_states, tactics, premises = extract_mathlib4_proofs()
    
    if not proof_states:
        print("❌ No proofs extracted from mathlib4")
        return
    
    # Save extracted data
    save_extracted_data(proof_states, tactics, premises)
    
    print(f"\n🎉 Extraction Summary:")
    print(f"   Proofs: {len(proof_states)}")
    print(f"   Tactics: {len(tactics)}")
    print(f"   Premises: {len(premises)}")
    print(f"   ID Range: {START_ID} - {START_ID + len(proof_states) - 1}")

if __name__ == "__main__":
    main()