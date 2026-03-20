#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
MAXIMUM CoqGym Extraction - Extract ALL available proofs

Uses comprehensive regex patterns and processes ALL .v files.
"""

import json
import os
import re
from typing import Dict, List, Any, Tuple
import multiprocessing
from concurrent.futures import ProcessPoolExecutor

# Configuration
COQGYM_DIR = "external_corpora/CoqGym"
OUTPUT_DIR = "training_data"
PROOF_STATES_FILE = f"{OUTPUT_DIR}/proof_states_coqgym_max.jsonl"
TACTICS_FILE = f"{OUTPUT_DIR}/tactics_coqgym_max.jsonl"
PREMISES_FILE = f"{OUTPUT_DIR}/premises_coqgym_max.jsonl"
STATS_FILE = f"{OUTPUT_DIR}/stats_coqgym_max.json"

# Start ID after current max (47742 + buffer)
START_ID = 50000

def extract_file_proofs(filepath: str) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], List[Dict[str, Any]], int]:
    """Extract all proofs from a single Coq file."""
    
    proof_states = []
    tactics = []
    premises = []
    file_id = START_ID  # Will be adjusted by caller
    
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        # Comprehensive theorem/lemma patterns
        patterns = [
            (r'Theorem\s+([a-zA-Z0-9_\'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\Z))', 'theorem'),
            (r'Lemma\s+([a-zA-Z0-9_\'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\Z))', 'lemma'),
            (r'Proposition\s+([a-zA-Z0-9_\'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\Z))', 'proposition'),
            (r'Corollary\s+([a-zA-Z0-9_\'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\Z))', 'corollary'),
            (r'Fact\s+([a-zA-Z0-9_\'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\Z))', 'fact'),
            (r'Remark\s+([a-zA-Z0-9_\'\.]+)\s*:\s*(.*?)(?=\n\s*(?:Proof\.|Qed\.|Defined\.|\Z))', 'remark')
        ]
        
        for pattern, proof_type in patterns:
            for match in re.finditer(pattern, content, re.DOTALL):
                try:
                    name = match.group(1).strip()
                    statement = match.group(2).strip()
                    
                    if name and statement and len(name) < 200:  # Reasonable length
                        # Create proof state
                        proof_state = {
                            "id": file_id,
                            "prover": "Coq",
                            "theorem": name,
                            "goal": statement[:1000],  # Limit goal length
                            "context": [],
                            "source": "CoqGym",
                            "proof_type": proof_type
                        }
                        proof_states.append(proof_state)
                        
                        # Extract proof content (if available)
                        proof_start = match.end()
                        remaining = content[proof_start:]
                        proof_match = re.search(r'Proof\.(.*?)(?=\n\s*(?:Qed|Defined|Save)\.)', remaining, re.DOTALL)
                        
                        if proof_match:
                            proof_content = proof_match.group(1)
                            
                            # Extract tactics - comprehensive patterns
                            tactic_patterns = [
                                r'\.\s*([a-zA-Z0-9_]+)',  # Simple tactics
                                r'apply\s+([a-zA-Z0-9_\.]+)',  # apply tactic
                                r'intros?\s+([a-zA-Z0-9_\s]+)',  # intros
                                r'rewrite\s+([^\n]+)',  # rewrite
                                r'set\s+\(([^)]+)\)',  # set
                                r'pose\s+([^\n]+)',  # pose
                                r'assert\s+\(([^)]+)\)',  # assert
                            ]
                            
                            for step, (tactic_pattern, tactic_type) in enumerate(tactic_patterns):
                                for tactic_match in re.finditer(tactic_pattern, proof_content):
                                    tactic = tactic_match.group(1).strip()
                                    if tactic and len(tactic) < 100:
                                        tactics.append({
                                            "proof_id": file_id,
                                            "step": step + 1,
                                            "tactic": tactic,
                                            "prover": "Coq",
                                            "tactic_type": tactic_type
                                        })
                            
                            # Extract premises/hypotheses
                            hyp_patterns = [
                                r'intros?\s+([a-zA-Z0-9_\s]+)',
                                r'pose\s+([a-zA-Z0-9_]+)\s*:=',
                                r'assert\s+\(([a-zA-Z0-9_]+):'
                            ]
                            
                            for hyp_pattern in hyp_patterns:
                                for hyp_match in re.finditer(hyp_pattern, proof_content):
                                    hyps = hyp_match.group(1).strip().split()
                                    for hyp in hyps:
                                        if hyp and len(hyp) < 50:
                                            premises.append({
                                                "proof_id": file_id,
                                                "premise": hyp,
                                                "prover": "Coq",
                                                "theorem": name,
                                                "source": "CoqGym"
                                            })
                        
                        file_id += 1
                except Exception as e:
                    continue  # Skip problematic matches
        
        return proof_states, tactics, premises, file_id - START_ID
    
    except Exception as e:
        print(f"⚠️  Error processing {filepath}: {e}")
        return [], [], [], 0

def process_file(args: tuple) -> tuple:
    """Wrapper for multiprocessing."""
    filepath, base_id = args
    return extract_file_proofs(filepath), base_id

def max_extract_coqgym():
    """Maximum extraction from all CoqGym files."""
    
    print("🚀 MAXIMUM CoqGym Extraction")
    print("=" * 50)
    
    # Find ALL .v files
    coqgym_proofs_dir = os.path.join(COQGYM_DIR, "coq_projects")
    
    if not os.path.exists(coqgym_proofs_dir):
        print(f"❌ CoqGym directory not found: {coqgym_proofs_dir}")
        return
    
    # Get all .v files
    v_files = []
    for root, dirs, files in os.walk(coqgym_proofs_dir):
        for file in files:
            if file.endswith('.v'):
                v_files.append(os.path.join(root, file))
    
    print(f"🔍 Found {len(v_files)} Coq files to process")
    
    # Process files in parallel batches
    all_proof_states = []
    all_tactics = []
    all_premises = []
    current_id = START_ID
    batch_size = 100
    
    for i in range(0, len(v_files), batch_size):
        batch = v_files[i:i + batch_size]
        print(f"📦 Processing batch {i//batch_size + 1}/{len(v_files)//batch_size + 1} ({len(batch)} files)...")
        
        batch_results = []
        for filepath in batch:
            try:
                proofs, tactics, premises, count = extract_file_proofs(filepath)
                if count > 0:
                    all_proof_states.extend(proofs)
                    all_tactics.extend(tactics)
                    all_premises.extend(premises)
                    current_id += count
                    batch_results.append((filepath, count))
            except Exception as e:
                print(f"❌ Error in {filepath}: {e}")
        
        # Show batch progress
        successful = len([r for r in batch_results if r[1] > 0])
        total_count = sum(r[1] for r in batch_results)
        print(f"  ✅ Batch complete: {successful}/{len(batch)} files, {total_count} proofs extracted")
        
        # Save progress periodically
        if len(all_proof_states) >= 1000:
            save_extracted_data(all_proof_states, all_tactics, all_premises, current_id)
            print(f"💾 Checkpoint saved: {len(all_proof_states)} proofs so far")
    
    # Final save
    save_extracted_data(all_proof_states, all_tactics, all_premises, current_id)
    
    print(f"\n🎉 MAXIMUM Extraction Complete!")
    print(f"   Total Proofs: {len(all_proof_states)}")
    print(f"   Total Tactics: {len(all_tactics)}")
    print(f"   Total Premises: {len(all_premises)}")
    print(f"   ID Range: {START_ID} - {current_id - 1}")

def save_extracted_data(proof_states: List[Dict[str, Any]], 
                       tactics: List[Dict[str, Any]], 
                       premises: List[Dict[str, Any]], 
                       next_id: int):
    """Save extracted data with progress tracking."""
    
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    
    # Save with temporary files first
    temp_states = PROOF_STATES_FILE + ".tmp"
    temp_tactics = TACTICS_FILE + ".tmp"
    temp_premises = PREMISES_FILE + ".tmp"
    
    try:
        # Save proof states
        with open(temp_states, 'w', encoding='utf-8') as f:
            for state in proof_states:
                f.write(json.dumps(state, ensure_ascii=False) + '\n')
        
        # Save tactics
        with open(temp_tactics, 'w', encoding='utf-8') as f:
            for tactic in tactics:
                f.write(json.dumps(tactic, ensure_ascii=False) + '\n')
        
        # Save premises
        with open(temp_premises, 'w', encoding='utf-8') as f:
            for premise in premises:
                f.write(json.dumps(premise, ensure_ascii=False) + '\n')
        
        # Atomic rename
        if os.path.exists(PROOF_STATES_FILE):
            os.remove(PROOF_STATES_FILE)
        os.rename(temp_states, PROOF_STATES_FILE)
        
        if os.path.exists(TACTICS_FILE):
            os.remove(TACTICS_FILE)
        os.rename(temp_tactics, TACTICS_FILE)
        
        if os.path.exists(PREMISES_FILE):
            os.remove(PREMISES_FILE)
        os.rename(temp_premises, PREMISES_FILE)
        
        # Save statistics
        stats = {
            "source": "CoqGym_MAX",
            "extraction_date": "2026-03-20",
            "proof_states_count": len(proof_states),
            "tactics_count": len(tactics),
            "premises_count": len(premises),
            "start_id": START_ID,
            "end_id": next_id - 1,
            "files_processed": len([f for f in os.listdir(COQGYM_DIR) if f.endswith('.v')]),
            "extraction_method": "comprehensive_regex"
        }
        
        with open(STATS_FILE, 'w', encoding='utf-8') as f:
            json.dump(stats, f, indent=2)
        
        print(f"✅ Saved progress: {len(proof_states)} proofs, {len(tactics)} tactics, {len(premises)} premises")
        
    except Exception as e:
        print(f"❌ Error saving data: {e}")
        # Clean up temp files
        for temp_file in [temp_states, temp_tactics, temp_premises]:
            if os.path.exists(temp_file):
                os.remove(temp_file)

if __name__ == "__main__":
    max_extract_coqgym()