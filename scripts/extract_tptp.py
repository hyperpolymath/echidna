#!/usr/bin/env python3
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# TPTP Problem Library extractor for ECHIDNA training data.
# Reads .p files from the TPTP library and extracts proof states
# for first-order ATP backends: Vampire, E Prover, SPASS.
#
# Input:  external_corpora/tptp/ (TPTP problem files)
# Output: training_data/proof_states_tptp.jsonl
#         training_data/tactics_tptp.jsonl
#         training_data/stats_tptp.json

import json
import os
import re
import glob
from datetime import datetime
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# ID range for TPTP-sourced proof states
ID_BASE = 70000

# Map TPTP domain prefixes to the most natural ATP prover.
# We round-robin across all three to keep the corpus balanced.
PROVERS = ["Vampire", "EProver", "SPASS"]

# TPTP status values that indicate a provable theorem
PROVABLE_STATUSES = {
    "Theorem", "Unsatisfiable", "ContradictoryAxioms",
    "CounterSatisfiable", "Satisfiable",
}

# ---------------------------------------------------------------------------
# Parser helpers
# ---------------------------------------------------------------------------

def strip_tptp_comments(text):
    """Remove TPTP block comments (/% ... %/) and line comments (% ...)."""
    # Block comments first
    text = re.sub(r'/%.*?%/', '', text, flags=re.DOTALL)
    # Line comments
    text = re.sub(r'%[^\n]*', '', text)
    return text


def parse_tptp_file(filepath):
    """Parse a single .p TPTP problem file.

    Returns a dict with:
        name        - problem name (from filename)
        status      - SZS status annotation if present
        domain      - TPTP domain code (e.g. 'AGT', 'ALG')
        conjecture  - the conjecture formula (string) or None
        axioms      - list of axiom formula strings
        includes    - list of include directives
    """
    name = Path(filepath).stem
    domain = re.match(r'^([A-Z]+)', name)
    domain = domain.group(1) if domain else "UNK"

    try:
        with open(filepath, 'r', errors='replace') as fh:
            raw = fh.read()
    except (OSError, IOError):
        return None

    # Extract SZS status from header comments
    status_match = re.search(r'%\s*Status\s*:\s*(\w+)', raw)
    status = status_match.group(1) if status_match else "Unknown"

    cleaned = strip_tptp_comments(raw)

    # Parse formulae: fof(...), cnf(...), tff(...), thf(...)
    formula_pat = re.compile(
        r'(fof|cnf|tff|thf)\s*\(\s*'   # language
        r"([^,]+)\s*,\s*"               # name
        r"(\w+)\s*,\s*"                 # role
        r"(.*?)\s*\)\s*\.",             # formula body
        re.DOTALL,
    )

    conjecture = None
    axioms = []
    includes = re.findall(r"include\(\s*'([^']+)'\s*\)", cleaned)

    for match in formula_pat.finditer(cleaned):
        _lang, _fname, role, body = match.groups()
        role = role.strip().lower()
        body = ' '.join(body.split())  # normalise whitespace

        if role == "conjecture":
            conjecture = body
        elif role in ("axiom", "hypothesis", "lemma", "definition",
                       "assumption", "type", "plain"):
            axioms.append(body)

    return {
        "name": name,
        "status": status,
        "domain": domain,
        "conjecture": conjecture,
        "axioms": axioms,
        "includes": includes,
    }


# ---------------------------------------------------------------------------
# Extraction pipeline
# ---------------------------------------------------------------------------

def find_tptp_files(base_dir):
    """Recursively find all .p files under base_dir."""
    results = []
    for root, _dirs, files in os.walk(base_dir):
        for fname in files:
            if fname.endswith('.p'):
                results.append(os.path.join(root, fname))
    results.sort()
    return results


def extract_all(base_dir):
    """Extract training data from the TPTP corpus.

    Returns (proof_states, tactics, stats_dict).
    """
    files = find_tptp_files(base_dir)
    print(f"Found {len(files)} .p files in {base_dir}")

    proof_states = []
    tactics = []
    prover_counts = {p: 0 for p in PROVERS}
    skipped = 0
    errors = 0

    for idx, fpath in enumerate(files):
        parsed = parse_tptp_file(fpath)
        if parsed is None:
            errors += 1
            continue

        # We want problems that have a conjecture (something to prove)
        if parsed["conjecture"] is None:
            skipped += 1
            continue

        record_id = ID_BASE + len(proof_states)

        # Round-robin prover assignment for balanced corpus
        prover = PROVERS[len(proof_states) % len(PROVERS)]

        # Build context from axioms (limit to first 20 to keep size sane)
        context = parsed["axioms"][:20]

        state = {
            "id": record_id,
            "prover": prover,
            "theorem": parsed["name"],
            "goal": parsed["conjecture"],
            "context": context,
            "source": "TPTP",
            "status": parsed["status"],
            "domain": parsed["domain"],
            "proof_steps": len(parsed["axioms"]),
        }
        proof_states.append(state)
        prover_counts[prover] += 1

        # Tactic record: for ATP the "tactic" is running the solver
        tactic = {
            "proof_id": record_id,
            "step": 1,
            "tactic": f"atp_solve_{prover.lower()}",
            "prover": prover,
            "proof_text": f"% TPTP {parsed['status']} via {prover}",
        }
        tactics.append(tactic)

        # Progress indicator every 5000 files
        if (idx + 1) % 5000 == 0:
            print(f"  processed {idx + 1}/{len(files)} files ...")

    stats = {
        "version": "v2.0-tptp",
        "extraction_date": datetime.now().isoformat(),
        "total_files_scanned": len(files),
        "total_proofs": len(proof_states),
        "total_tactics": len(tactics),
        "skipped_no_conjecture": skipped,
        "read_errors": errors,
        "prover_distribution": prover_counts,
        "source": "TPTP Problem Library",
        "id_range": f"{ID_BASE}-{ID_BASE + len(proof_states) - 1}" if proof_states else "none",
    }

    return proof_states, tactics, stats


def save_results(proof_states, tactics, stats, output_dir="training_data"):
    """Write extraction results to JSONL / JSON files."""
    out = Path(output_dir)
    out.mkdir(exist_ok=True)

    with open(out / "proof_states_tptp.jsonl", 'w') as fh:
        for rec in proof_states:
            fh.write(json.dumps(rec) + '\n')

    with open(out / "tactics_tptp.jsonl", 'w') as fh:
        for rec in tactics:
            fh.write(json.dumps(rec) + '\n')

    with open(out / "stats_tptp.json", 'w') as fh:
        json.dump(stats, fh, indent=2)

    print(f"\nSaved {len(proof_states)} proof states -> {out}/proof_states_tptp.jsonl")
    print(f"Saved {len(tactics)} tactics        -> {out}/tactics_tptp.jsonl")
    print(f"Saved stats                        -> {out}/stats_tptp.json")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 60)
    print("ECHIDNA TPTP Extractor")
    print("Covers: Vampire, E Prover, SPASS")
    print("=" * 60)

    base_dir = "external_corpora/tptp"
    if not Path(base_dir).is_dir():
        print(f"ERROR: Corpus directory not found: {base_dir}")
        print("Download TPTP first (see CORPUS_EXPANSION_PLAN.md).")
        return 1

    proof_states, tactics, stats = extract_all(base_dir)

    if not proof_states:
        print("\nWARNING: No proof states extracted. Check corpus contents.")
        return 1

    save_results(proof_states, tactics, stats)

    print(f"\nProver distribution:")
    for prover, count in stats["prover_distribution"].items():
        print(f"  {prover:12s}: {count}")

    print(f"\nTotal: {stats['total_proofs']} proof states (ID range {stats['id_range']})")
    return 0


if __name__ == "__main__":
    exit(main())
