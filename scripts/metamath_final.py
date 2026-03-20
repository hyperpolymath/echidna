#!/usr/bin/env python3
# SPDX-License-Identifier: PMPL-1.0-or-later
# Final Metamath proof extractor - simplified and robust

import json
import re
from datetime import datetime
from pathlib import Path

def extract_theorems(file_path):
    """Extract theorems from Metamath set.mm file"""
    theorems = []
    
    # Pattern: theorem_name $p statement $= proof $.
    pattern = re.compile(r'^\s*([a-zA-Z0-9._-]+)\s+\$p\s+([^$]+)\$=\s*([^$]+)\$\.', re.MULTILINE)
    
    with open(file_path, 'r') as f:
        content = f.read()
        
        for match in pattern.finditer(content):
            name = match.group(1).strip()
            statement = match.group(2).strip()
            proof = match.group(3).strip()
            
            if name and proof:
                theorems.append({
                    'name': name,
                    'statement': statement,
                    'proof': proof
                })
    
    return theorems

def save_as_training_data(theorems):
    """Save extracted theorems as training data"""
    proof_states = []
    tactics = []
    
    for i, theorem in enumerate(theorems):
        # Proof state
        state = {
            "id": i + 1000,  # Start from 1000 to avoid conflicts
            "prover": "Metamath",
            "theorem": theorem['name'],
            "goal": theorem['statement'],
            "context": [],
            "source": "Metamath",
            "proof_steps": len(theorem['proof'].split())
        }
        proof_states.append(state)
        
        # Tactic
        tactic = {
            "proof_id": i + 1000,
            "step": 1,
            "tactic": "metamath_prove",
            "prover": "Metamath",
            "proof_text": theorem['proof']
        }
        tactics.append(tactic)
    
    # Save to files
    training_dir = Path("training_data")
    training_dir.mkdir(exist_ok=True)
    
    with open(training_dir / "proof_states_metamath.jsonl", 'w') as f:
        for state in proof_states:
            f.write(json.dumps(state) + '\n')
    
    with open(training_dir / "tactics_metamath.jsonl", 'w') as f:
        for tactic in tactics:
            f.write(json.dumps(tactic) + '\n')
    
    # Save stats
    stats = {
        "version": "v2.0-metamath-final",
        "extraction_date": datetime.now().isoformat(),
        "total_proofs": len(theorems),
        "total_tactics": len(theorems),
        "source": "Metamath set.mm",
        "prover": "Metamath"
    }
    
    with open(training_dir / "stats_metamath.json", 'w') as f:
        json.dump(stats, f, indent=2)
    
    print(f"✓ Extracted {len(theorems)} theorems from Metamath")
    if theorems:
        print(f"  Sample theorem: {theorems[0]['name']}")
        print(f"  Sample proof: {theorems[0]['proof'][:50]}...")
    print("  Files saved: proof_states_metamath.jsonl, tactics_metamath.jsonl")
    
    return len(theorems)

def main():
    print("Metamath Proof Extractor (Final)")
    print("===============================")
    
    file_path = "external_corpora/metamath/set.mm"
    
    if not Path(file_path).exists():
        print(f"Error: File not found: {file_path}")
        return 1
    
    print(f"\nExtracting from {file_path}...")
    theorems = extract_theorems(file_path)
    print(f"Found {len(theorems)} theorems")
    
    if theorems:
        print("\nFirst 10 theorems:")
        for i, theorem in enumerate(theorems[:10]):
            print(f"  {i+1}. {theorem['name']}")
    
    print("\nSaving training data...")
    save_as_training_data(theorems)
    
    return 0

if __name__ == "__main__":
    main()
