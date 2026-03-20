#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
MAXIMUM mathlib4 Extraction - Extract ALL available Lean proofs

Comprehensive extraction from all 8,324 .lean files.
"""

import json
import os
import re
from typing import Dict, List, Any, Tuple

# Configuration
MATHLIB4_DIR = "external_corpora/mathlib4"
OUTPUT_DIR = "training_data"
PROOF_STATES_FILE = f"{OUTPUT_DIR}/proof_states_mathlib4_max.jsonl"
TACTICS_FILE = f"{OUTPUT_DIR}/tactics_mathlib4_max.jsonl"
PREMISES_FILE = f"{OUTPUT_DIR}/premises_mathlib4_max.jsonl"
STATS_FILE = f"{OUTPUT_DIR}/stats_mathlib4_max.json"

# Start ID after CoqGym MAX (50000 + 10000 buffer = 60000)
START_ID = 60000

def extract_file_proofs(filepath: str, current_id: int) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], List[Dict[str, Any]], int]:
    """Extract all proofs from a single Lean file."""
    
    proof_states = []
    tactics = []
    premises = []
    file_id = current_id
    
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        # Comprehensive Lean proof patterns
        patterns = [
            (r'theorem\s+([a-zA-Z0-9_\'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\Z))', 'theorem'),
            (r'lemma\s+([a-zA-Z0-9_\'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\Z))', 'lemma'),
            (r'proposition\s+([a-zA-Z0-9_\'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\Z))', 'proposition'),
            (r'corollary\s+([a-zA-Z0-9_\'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\Z))', 'corollary'),
            (r'example\s+([a-zA-Z0-9_\'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\Z))', 'example'),
            (r'def\s+([a-zA-Z0-9_\'\.]+)\s*(.*?)(?=\n\s*(?::=|:=\s*by\s|@\[|\/--|\Z))', 'definition'),
        ]
        
        for pattern, proof_type in patterns:
            for match in re.finditer(pattern, content, re.DOTALL):
                try:
                    name = match.group(1).strip()
                    statement = match.group(2).strip()
                    
                    if name and statement and len(name) < 200:
                        # Create proof state
                        proof_state = {
                            "id": file_id,
                            "prover": "Lean",
                            "theorem": name,
                            "goal": statement[:1000],
                            "context": [],
                            "source": "mathlib4",
                            "proof_type": proof_type
                        }
                        proof_states.append(proof_state)
                        
                        # Extract proof content
                        proof_start = match.end()
                        remaining = content[proof_start:]
                        
                        # Look for "by" clause or tactic blocks
                        by_match = re.search(r':=\s*by\s+([^\n]+)', remaining)
                        tactic_block_match = re.search(r':=\s*\n\s*([\s\S]*?)(?=\n\s*(?:@\[|\/--|\Z))', remaining)
                        
                        if by_match:
                            # Simple "by" clause
                            tactics_str = by_match.group(1).strip()
                            individual_tactics = re.split(r'[\s,]+', tactics_str)
                            
                            for step, tactic in enumerate(individual_tactics):
                                if tactic and len(tactic) < 100:
                                    tactics.append({
                                        "proof_id": file_id,
                                        "step": step + 1,
                                        "tactic": tactic,
                                        "prover": "Lean",
                                        "tactic_type": "by_clause"
                                    })
                        elif tactic_block_match:
                            # Multi-line tactic block
                            tactic_content = tactic_block_match.group(1)
                            
                            # Extract individual tactics
                            tactic_lines = [line.strip() for line in tactic_content.split('\n') if line.strip()]
                            
                            for step, tactic_line in enumerate(tactic_lines):
                                if tactic_line and not tactic_line.startswith('--'):
                                    # Remove comments
                                    tactic = re.sub(r'--.*$', '', tactic_line).strip()
                                    if tactic and len(tactic) < 200:
                                        tactics.append({
                                            "proof_id": file_id,
                                            "step": step + 1,
                                            "tactic": tactic,
                                            "prover": "Lean",
                                            "tactic_type": "tactic_block"
                                        })
                        
                        # Extract premises/hypotheses
                        hyp_patterns = [
                            r'intro\s+([a-zA-Z0-9_\s]+)',
                            r'⟨([a-zA-Z0-9_\s,]+)⟩',
                            r'let\s+([a-zA-Z0-9_]+)\s*:=',
                            r'have\s+([a-zA-Z0-9_]+)\s*:=',
                        ]
                        
                        for hyp_pattern in hyp_patterns:
                            for hyp_match in re.finditer(hyp_pattern, remaining):
                                hyps = [h.strip() for h in hyp_match.group(1).split(',')]
                                for hyp in hyps:
                                    if hyp and len(hyp) < 50:
                                        premises.append({
                                            "proof_id": file_id,
                                            "premise": hyp,
                                            "prover": "Lean",
                                            "theorem": name,
                                            "source": "mathlib4"
                                        })
                        
                        file_id += 1
                except Exception as e:
                    continue
        
        return proof_states, tactics, premises, file_id - current_id
    
    except Exception as e:
        print(f"⚠️  Error processing {filepath}: {e}")
        return [], [], [], 0

def max_extract_mathlib4():
    """Maximum extraction from all mathlib4 files."""
    
    print("🚀 MAXIMUM mathlib4 Extraction")
    print("=" * 50)
    
    # Find ALL .lean files
    mathlib4_proofs_dir = os.path.join(MATHLIB4_DIR, "Mathlib")
    
    if not os.path.exists(mathlib4_proofs_dir):
        print(f"❌ mathlib4 directory not found: {mathlib4_proofs_dir}")
        return
    
    # Get all .lean files
    lean_files = []
    for root, dirs, files in os.walk(mathlib4_proofs_dir):
        for file in files:
            if file.endswith('.lean'):
                lean_files.append(os.path.join(root, file))
    
    print(f"🔍 Found {len(lean_files)} Lean files to process")
    
    # Process files in batches
    all_proof_states = []
    all_tactics = []
    all_premises = []
    current_id = START_ID
    batch_size = 50
    
    for i in range(0, len(lean_files), batch_size):
        batch = lean_files[i:i + batch_size]
        print(f"📦 Processing batch {i//batch_size + 1}/{len(lean_files)//batch_size + 1} ({len(batch)} files)...")
        
        batch_results = []
        for filepath in batch:
            try:
                proofs, tactics, premises, count = extract_file_proofs(filepath, current_id)
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
        if len(all_proof_states) >= 500:
            save_extracted_data(all_proof_states, all_tactics, all_premises, current_id)
            print(f"💾 Checkpoint saved: {len(all_proof_states)} proofs so far")
    
    # Final save
    save_extracted_data(all_proof_states, all_tactics, all_premises, current_id)
    
    print(f"\n🎉 MAXIMUM mathlib4 Extraction Complete!")
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
        for temp_file, final_file in [(temp_states, PROOF_STATES_FILE), 
                                      (temp_tactics, TACTICS_FILE), 
                                      (temp_premises, PREMISES_FILE)]:
            if os.path.exists(final_file):
                os.remove(final_file)
            os.rename(temp_file, final_file)
        
        # Save statistics
        stats = {
            "source": "mathlib4_MAX",
            "extraction_date": "2026-03-20",
            "proof_states_count": len(proof_states),
            "tactics_count": len(tactics),
            "premises_count": len(premises),
            "start_id": START_ID,
            "end_id": next_id - 1,
            "files_processed": len(lean_files) if 'lean_files' in locals() else 0,
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
    max_extract_mathlib4()