#!/usr/bin/env python3
# SPDX-License-Identifier: PMPL-1.0-or-later
# Metamath proof extractor

import json
import re
from datetime import datetime
from pathlib import Path

class Theorem:
    def __init__(self, name, statement, proof):
        self.name = name
        self.statement = statement
        self.proof = proof

def extract_theorems(file_path):
    """Extract theorems from Metamath set.mm file"""
    theorems = []
    
    with open(file_path, 'r') as f:
        for line in f:
            # Skip comment blocks and empty lines
            if line.startswith('$( ') or line.startswith('$)') or line.strip() == '':
                continue
            
            # Theorem declaration line (contains $p)
            if '$p' in line:
                # Extract theorem name (before $p)
                parts = line.split('$p')
                if len(parts) > 1:
                    name_part = parts[0].strip()
                    # Remove any trailing $.
                    name_part = re.sub(r'\$\.', '', name_part)
                    current_name = name_part.strip()
                    
                    # Extract statement (between $p and $=)
                    statement_part = parts[1]
                    statement_match = re.match(r'^\s*([^$]+)\$=', statement_part)
                    if statement_match:
                        current_statement = statement_match.group(1).strip()
                    else:
                        current_statement = ""
                    
                    # Extract proof (after $=)
                    proof_match = re.search(r'\$=\s*([^$]+)\$\.', statement_part)
                    if proof_match:
                        current_proof = proof_match.group(1).strip()
                        
                        # Save theorem
                        if current_name and current_proof:
                            theorems.append(Theorem(current_name, current_statement, current_proof))
    
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
            "theorem": theorem.name,
            "goal": theorem.statement,
            "context": [],
            "source": "Metamath",
            "proof_steps": len(theorem.proof.split())
        }
        proof_states.append(state)
        
        # Tactic
        tactic = {
            "proof_id": i + 1000,
            "step": 1,
            "tactic": "metamath_prove",
            "prover": "Metamath",
            "proof_text": theorem.proof
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
        "version": "v2.0-metamath-python",
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
        print(f"  Sample theorem: {theorems[0].name}")
    print("  Files saved: proof_states_metamath.jsonl, tactics_metamath.jsonl")
    
    return len(theorems)

def main():
    print("Metamath Proof Extractor")
    print("========================")
    
    file_path = "external_corpora/metamath/set.mm"
    
    if not Path(file_path).exists():
        print(f"Error: File not found: {file_path}")
        return 1
    
    print(f"\nExtracting from {file_path}...")
    theorems = extract_theorems(file_path)
    print(f"Found {len(theorems)} theorems")
    
    if theorems:
        print("\nFirst few theorems:")
        for i, theorem in enumerate(theorems[:5]):
            print(f"  {i+1}. {theorem.name}")
    
    print("\nSaving training data...")
    save_as_training_data(theorems)
    
    return 0

if __name__ == "__main__":
    main()
