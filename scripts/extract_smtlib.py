#!/usr/bin/env python3
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# SMT-LIB benchmark extractor for ECHIDNA training data.
# Reads .smt2 files from the SMT-LIB benchmark suite and extracts
# proof states for SMT solver backends: Z3, CVC5, Alt-Ergo.
#
# Input:  external_corpora/smtlib/ (SMT-LIB benchmark files)
# Output: training_data/proof_states_smtlib.jsonl
#         training_data/tactics_smtlib.jsonl
#         training_data/stats_smtlib.json

import json
import os
import re
from datetime import datetime
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# ID range for SMT-LIB-sourced proof states
ID_BASE = 80000

# Three SMT backends we target, round-robined for balance
PROVERS = ["Z3", "CVC5", "AltErgo"]

# SMT-LIB logics grouped by category for metadata
LOGIC_CATEGORIES = {
    "QF_LIA": "linear integer arithmetic",
    "QF_LRA": "linear real arithmetic",
    "QF_NIA": "nonlinear integer arithmetic",
    "QF_NRA": "nonlinear real arithmetic",
    "QF_BV": "bitvectors",
    "QF_UF": "uninterpreted functions",
    "QF_UFLIA": "UF + linear integer arithmetic",
    "QF_UFLRA": "UF + linear real arithmetic",
    "QF_AUFLIA": "arrays + UF + LIA",
    "QF_ABV": "arrays + bitvectors",
    "QF_AUFBV": "arrays + UF + bitvectors",
    "LIA": "linear integer arithmetic",
    "LRA": "linear real arithmetic",
    "UFLIA": "UF + linear integer arithmetic",
    "AUFLIRA": "arrays + UF + LIA + LRA",
    "AUFNIRA": "arrays + UF + nonlinear mixed arithmetic",
}

# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

def parse_smt2_file(filepath):
    """Parse a single .smt2 SMT-LIB benchmark file.

    Returns a dict with:
        name          - benchmark name (from filename or set-info)
        logic         - declared logic (e.g. QF_LIA)
        status        - expected result (sat/unsat/unknown)
        assertions    - list of (assert ...) expressions
        declarations  - list of (declare-fun/sort/const ...) expressions
        check_sat     - whether (check-sat) is present
    """
    name = Path(filepath).stem
    logic = "UNKNOWN"
    status = "unknown"
    assertions = []
    declarations = []
    has_check_sat = False

    try:
        with open(filepath, 'r', errors='replace') as fh:
            content = fh.read()
    except (OSError, IOError):
        return None

    # Extract logic
    logic_match = re.search(r'\(\s*set-logic\s+(\S+)\s*\)', content)
    if logic_match:
        logic = logic_match.group(1)

    # Extract status from set-info
    status_match = re.search(r':status\s+(sat|unsat|unknown)', content, re.IGNORECASE)
    if status_match:
        status = status_match.group(1).lower()

    # Extract benchmark name from set-info if available
    name_match = re.search(r':source\s*\|([^|]*)\|', content)
    if not name_match:
        name_match = re.search(r':source\s+"([^"]*)"', content)

    # Extract declarations (declare-fun, declare-sort, declare-const,
    # define-fun, define-sort)
    decl_pat = re.compile(
        r'\(\s*(declare-fun|declare-sort|declare-const|define-fun|define-sort)'
        r'\s+([^)]*(?:\([^)]*\))*[^)]*)\)',
    )
    for match in decl_pat.finditer(content):
        decl_text = f"({match.group(1)} {match.group(2)})"
        # Keep declarations concise (truncate very long ones)
        if len(decl_text) <= 500:
            declarations.append(decl_text)

    # Extract assertions using balanced-paren matching
    assertions = extract_balanced_sexps(content, "assert")

    # Check for (check-sat)
    has_check_sat = bool(re.search(r'\(\s*check-sat\s*\)', content))

    return {
        "name": name,
        "logic": logic,
        "status": status,
        "assertions": assertions,
        "declarations": declarations,
        "check_sat": has_check_sat,
    }


def extract_balanced_sexps(text, keyword):
    """Extract top-level S-expressions starting with (keyword ...).

    Uses a simple balanced-parenthesis counter. Returns a list of
    the inner expression strings (without the outer keyword wrapper).
    """
    results = []
    pattern = re.compile(r'\(\s*' + re.escape(keyword) + r'\s+')

    for match in pattern.finditer(text):
        start = match.start()
        depth = 0
        i = start
        while i < len(text):
            if text[i] == '(':
                depth += 1
            elif text[i] == ')':
                depth -= 1
                if depth == 0:
                    # Full expression from start to i (inclusive)
                    inner = text[match.end():i].strip()
                    # Truncate very large assertions
                    if len(inner) <= 1000:
                        results.append(inner)
                    else:
                        results.append(inner[:997] + "...")
                    break
            i += 1

    return results


# ---------------------------------------------------------------------------
# Extraction pipeline
# ---------------------------------------------------------------------------

def find_smt2_files(base_dir, max_files=50000):
    """Recursively find .smt2 files, capped at max_files for sanity."""
    results = []
    for root, _dirs, files in os.walk(base_dir):
        for fname in sorted(files):
            if fname.endswith('.smt2'):
                results.append(os.path.join(root, fname))
                if len(results) >= max_files:
                    return results
    results.sort()
    return results


def extract_all(base_dir):
    """Extract training data from the SMT-LIB corpus.

    Returns (proof_states, tactics, stats_dict).
    """
    files = find_smt2_files(base_dir)
    print(f"Found {len(files)} .smt2 files in {base_dir}")

    proof_states = []
    tactics = []
    prover_counts = {p: 0 for p in PROVERS}
    logic_counts = {}
    status_counts = {"sat": 0, "unsat": 0, "unknown": 0}
    skipped = 0
    errors = 0

    for idx, fpath in enumerate(files):
        parsed = parse_smt2_file(fpath)
        if parsed is None:
            errors += 1
            continue

        # We want benchmarks that actually have assertions
        if not parsed["assertions"]:
            skipped += 1
            continue

        record_id = ID_BASE + len(proof_states)

        # Round-robin prover assignment
        prover = PROVERS[len(proof_states) % len(PROVERS)]

        # Build the goal from the primary assertion(s)
        # For multi-assertion benchmarks, combine them
        if len(parsed["assertions"]) == 1:
            goal = parsed["assertions"][0]
        else:
            # Show first assertion as goal, rest in context
            goal = parsed["assertions"][0]

        # Context: declarations + remaining assertions (limit for size)
        context = parsed["declarations"][:10]
        if len(parsed["assertions"]) > 1:
            context.extend(parsed["assertions"][1:10])

        state = {
            "id": record_id,
            "prover": prover,
            "theorem": parsed["name"],
            "goal": goal,
            "context": context,
            "source": "SMT-LIB",
            "logic": parsed["logic"],
            "status": parsed["status"],
            "proof_steps": len(parsed["assertions"]),
        }
        proof_states.append(state)
        prover_counts[prover] += 1

        # Track logic distribution
        logic = parsed["logic"]
        logic_counts[logic] = logic_counts.get(logic, 0) + 1

        # Track status distribution
        s = parsed["status"]
        if s in status_counts:
            status_counts[s] += 1

        # Tactic record
        tactic = {
            "proof_id": record_id,
            "step": 1,
            "tactic": f"smt_solve_{prover.lower()}",
            "prover": prover,
            "proof_text": f"; SMT-LIB {parsed['logic']} {parsed['status']} via {prover}",
        }
        tactics.append(tactic)

        # Progress indicator every 5000
        if (idx + 1) % 5000 == 0:
            print(f"  processed {idx + 1}/{len(files)} files ...")

    stats = {
        "version": "v2.0-smtlib",
        "extraction_date": datetime.now().isoformat(),
        "total_files_scanned": len(files),
        "total_proofs": len(proof_states),
        "total_tactics": len(tactics),
        "skipped_no_assertions": skipped,
        "read_errors": errors,
        "prover_distribution": prover_counts,
        "logic_distribution": dict(sorted(logic_counts.items(), key=lambda x: -x[1])),
        "status_distribution": status_counts,
        "source": "SMT-LIB Benchmarks",
        "id_range": f"{ID_BASE}-{ID_BASE + len(proof_states) - 1}" if proof_states else "none",
    }

    return proof_states, tactics, stats


def save_results(proof_states, tactics, stats, output_dir="training_data"):
    """Write extraction results to JSONL / JSON files."""
    out = Path(output_dir)
    out.mkdir(exist_ok=True)

    with open(out / "proof_states_smtlib.jsonl", 'w') as fh:
        for rec in proof_states:
            fh.write(json.dumps(rec) + '\n')

    with open(out / "tactics_smtlib.jsonl", 'w') as fh:
        for rec in tactics:
            fh.write(json.dumps(rec) + '\n')

    with open(out / "stats_smtlib.json", 'w') as fh:
        json.dump(stats, fh, indent=2)

    print(f"\nSaved {len(proof_states)} proof states -> {out}/proof_states_smtlib.jsonl")
    print(f"Saved {len(tactics)} tactics        -> {out}/tactics_smtlib.jsonl")
    print(f"Saved stats                        -> {out}/stats_smtlib.json")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 60)
    print("ECHIDNA SMT-LIB Extractor")
    print("Covers: Z3, CVC5, Alt-Ergo")
    print("=" * 60)

    base_dir = "external_corpora/smtlib"
    if not Path(base_dir).is_dir():
        print(f"ERROR: Corpus directory not found: {base_dir}")
        print("Download SMT-LIB benchmarks first (see CORPUS_EXPANSION_PLAN.md).")
        return 1

    proof_states, tactics, stats = extract_all(base_dir)

    if not proof_states:
        print("\nWARNING: No proof states extracted. Check corpus contents.")
        return 1

    save_results(proof_states, tactics, stats)

    print(f"\nProver distribution:")
    for prover, count in stats["prover_distribution"].items():
        print(f"  {prover:12s}: {count}")

    print(f"\nTop logics:")
    for logic, count in list(stats["logic_distribution"].items())[:10]:
        desc = LOGIC_CATEGORIES.get(logic, "")
        print(f"  {logic:15s}: {count:6d}  {desc}")

    print(f"\nStatus distribution:")
    for s, count in stats["status_distribution"].items():
        print(f"  {s:10s}: {count}")

    print(f"\nTotal: {stats['total_proofs']} proof states (ID range {stats['id_range']})")
    return 0


if __name__ == "__main__":
    exit(main())
