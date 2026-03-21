#!/usr/bin/env python3
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# merge_corpus.py — Merge all ECHIDNA corpus extraction results into a unified
# training file. Reads per-prover proof_states_*.jsonl files, deduplicates by
# (prover, theorem) pair (keeping the entry with richer context), assigns fresh
# sequential IDs, and writes:
#   - training_data/proof_states_UNIFIED.jsonl   (deduplicated corpus)
#   - training_data/stats_UNIFIED.json           (summary statistics)
#   - training_data/vocabulary_UNIFIED.txt        (vocabulary from goals/theorems)

import json
import os
import re
import sys
from collections import Counter, defaultdict
from datetime import date

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

TRAINING_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)),
                            "training_data")

# Per-prover source files — the authoritative extractions.
# We list them explicitly to avoid pulling in aggregate/merged files
# (ABSOLUTE_COMPLETE, ULTIMATE, FINAL_BALANCED, COMPLETE, all, v2, etc.).
PER_PROVER_FILES = [
    "proof_states_mathlib4_max.jsonl",   # Lean 4 / mathlib4 (113K)
    "proof_states_coqgym_max.jsonl",     # Coq (15K)
    "proof_states_smtlib.jsonl",         # Z3/CVC5/Alt-Ergo (20K)
    "proof_states_metamath.jsonl",       # Metamath (47K)
    "proof_states_hol_light.jsonl",      # HOL Light (7K)
    "proof_states_hol4.jsonl",           # HOL4 (1.9K)
    "proof_states_acl2.jsonl",           # ACL2
    "proof_states_pvs.jsonl",            # PVS
    "proof_states_why3.jsonl",           # Why3
    "proof_states_dafny.jsonl",          # Dafny
    "proof_states_fstar.jsonl",          # F*
    "proof_states_idris2.jsonl",         # Idris2
    "proof_states_mizar.jsonl",          # Mizar
    "proof_states_nuprl.jsonl",          # Nuprl (synthetic)
    "proof_states_minlog.jsonl",         # Minlog (synthetic)
    "proof_states_twelf.jsonl",          # Twelf (synthetic)
    "proof_states_imandra.jsonl",        # Imandra (synthetic)
    "proof_states_minizinc.jsonl",       # MiniZinc / constraint solvers
    "proof_states_mathlib4.jsonl",       # Additional mathlib4 (smaller set)
    "proof_states_coqgym.jsonl",         # Additional CoqGym (smaller set)
    "proof_states_2026-03-20.jsonl",     # Dated snapshot
]

# The 30 prover backends ECHIDNA supports.
ALL_PROVERS = {
    "Lean", "Lean4", "Coq", "Rocq", "Agda", "Isabelle", "Idris2", "Fstar", "F*",
    "Z3", "CVC5", "CVC4", "Alt-Ergo", "AltErgo",
    "Dafny", "Why3",
    "Metamath", "HOLLight", "HOL Light", "Mizar", "HOL4", "PVS", "ACL2",
    "TLAPS", "Twelf", "Nuprl", "Minlog", "Imandra",
    "Vampire", "EProver", "E Prover", "SPASS",
    "GLPK", "SCIP", "MiniZinc", "Chuffed", "ORTools", "OR-Tools",
}

# Canonical prover name mapping (normalise variants).
PROVER_CANONICAL = {
    "Lean4": "Lean",
    "Rocq": "Coq",
    "Fstar": "F*",
    "CVC4": "CVC5",
    "AltErgo": "Alt-Ergo",
    "HOL Light": "HOLLight",
    "E Prover": "EProver",
    "OR-Tools": "ORTools",
}

# Total expected backend count for coverage calculation.
TOTAL_BACKENDS = 30


def canonical_prover(name: str) -> str:
    """Return the canonical prover name for deduplication."""
    return PROVER_CANONICAL.get(name, name)


def context_richness(entry: dict) -> int:
    """Score how rich the context of a proof entry is.

    Higher is better — used to pick the best duplicate.
    """
    score = 0
    goal = entry.get("goal", "")
    score += len(goal)
    ctx = entry.get("context", [])
    if isinstance(ctx, list):
        score += sum(len(str(c)) for c in ctx)
    if entry.get("tactic_proof"):
        score += len(str(entry["tactic_proof"])) * 2
    if entry.get("proof_steps"):
        score += int(entry["proof_steps"]) * 5
    if entry.get("proof_type"):
        score += 10
    if entry.get("logic"):
        score += 10
    return score


def load_jsonl(filepath: str) -> list:
    """Load a JSONL file, skipping malformed lines."""
    entries = []
    if not os.path.isfile(filepath):
        return entries
    with open(filepath, "r", encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.strip()
            if not line:
                continue
            try:
                entry = json.loads(line)
                entries.append(entry)
            except json.JSONDecodeError:
                print(f"  WARN: Skipped malformed JSON at {os.path.basename(filepath)}:{lineno}")
    return entries


def extract_words(text: str) -> set:
    """Extract alphabetic tokens from text for vocabulary building."""
    # Split on non-alphanumeric, keep tokens >= 3 chars that are alphabetic.
    tokens = re.split(r"[^a-zA-Z]+", text)
    return {t.lower() for t in tokens if len(t) >= 3 and t.isalpha()}


def main():
    print("=" * 70)
    print("ECHIDNA Corpus Merge — merge_corpus.py")
    print("=" * 70)

    # ------------------------------------------------------------------
    # 1. Load all per-prover files
    # ------------------------------------------------------------------
    all_entries = []
    file_counts = {}

    for fname in PER_PROVER_FILES:
        fpath = os.path.join(TRAINING_DIR, fname)
        entries = load_jsonl(fpath)
        file_counts[fname] = len(entries)
        if entries:
            print(f"  Loaded {len(entries):>7,} proofs from {fname}")
        else:
            print(f"  SKIP   {fname} (not found or empty)")
        all_entries.extend(entries)

    print(f"\nTotal raw entries loaded: {len(all_entries):,}")

    # ------------------------------------------------------------------
    # 2. Deduplicate by (canonical_prover, theorem)
    # ------------------------------------------------------------------
    best = {}  # (prover, theorem) -> entry
    for entry in all_entries:
        prover = canonical_prover(entry.get("prover", "Unknown"))
        theorem = entry.get("theorem", "")
        key = (prover, theorem)
        if key not in best or context_richness(entry) > context_richness(best[key]):
            # Store with canonical prover name
            entry_copy = dict(entry)
            entry_copy["prover"] = prover
            best[key] = entry_copy

    deduped = list(best.values())
    print(f"After deduplication: {len(deduped):,} unique (prover, theorem) pairs")
    print(f"Duplicates removed:  {len(all_entries) - len(deduped):,}")

    # ------------------------------------------------------------------
    # 3. Assign fresh sequential IDs and sort by prover then theorem
    # ------------------------------------------------------------------
    deduped.sort(key=lambda e: (e.get("prover", ""), e.get("theorem", "")))
    for idx, entry in enumerate(deduped, start=1):
        entry["id"] = idx

    # ------------------------------------------------------------------
    # 4. Write unified JSONL
    # ------------------------------------------------------------------
    unified_path = os.path.join(TRAINING_DIR, "proof_states_UNIFIED.jsonl")
    with open(unified_path, "w", encoding="utf-8") as fh:
        for entry in deduped:
            fh.write(json.dumps(entry, ensure_ascii=False) + "\n")
    print(f"\nWrote {len(deduped):,} proofs to {unified_path}")

    # ------------------------------------------------------------------
    # 5. Compute statistics
    # ------------------------------------------------------------------
    prover_counts = Counter()
    source_counts = Counter()
    unique_theorems = set()
    vocab = set()

    for entry in deduped:
        prover_counts[entry.get("prover", "Unknown")] += 1
        source_counts[entry.get("source", "unknown")] += 1
        unique_theorems.add(entry.get("theorem", ""))
        # Vocabulary extraction
        goal_text = entry.get("goal", "")
        theorem_text = entry.get("theorem", "")
        vocab.update(extract_words(goal_text))
        vocab.update(extract_words(theorem_text))

    provers_with_data = len([p for p, c in prover_counts.items() if c > 0])
    coverage_pct = round(provers_with_data / TOTAL_BACKENDS * 100, 1)

    stats = {
        "version": "UNIFIED",
        "date": str(date.today()),
        "total_proofs": len(deduped),
        "unique_theorems": len(unique_theorems),
        "provers_with_data": provers_with_data,
        "total_backends": TOTAL_BACKENDS,
        "coverage_percentage": coverage_pct,
        "per_prover_counts": dict(sorted(prover_counts.items(),
                                         key=lambda x: -x[1])),
        "per_source_counts_top50": dict(
            sorted(source_counts.items(), key=lambda x: -x[1])[:50]
        ),
        "vocabulary_size": len(vocab),
        "source_files_used": file_counts,
    }

    stats_path = os.path.join(TRAINING_DIR, "stats_UNIFIED.json")
    with open(stats_path, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2, ensure_ascii=False)
    print(f"Wrote statistics to {stats_path}")

    # ------------------------------------------------------------------
    # 6. Write vocabulary file
    # ------------------------------------------------------------------
    vocab_path = os.path.join(TRAINING_DIR, "vocabulary_UNIFIED.txt")
    with open(vocab_path, "w", encoding="utf-8") as fh:
        for word in sorted(vocab):
            fh.write(word + "\n")
    print(f"Wrote {len(vocab):,} vocabulary words to {vocab_path}")

    # ------------------------------------------------------------------
    # 7. Summary
    # ------------------------------------------------------------------
    print("\n" + "=" * 70)
    print("UNIFIED CORPUS SUMMARY")
    print("=" * 70)
    print(f"  Total proofs:        {len(deduped):>10,}")
    print(f"  Unique theorems:     {len(unique_theorems):>10,}")
    print(f"  Vocabulary words:    {len(vocab):>10,}")
    print(f"  Provers with data:   {provers_with_data:>10} / {TOTAL_BACKENDS}")
    print(f"  Coverage:            {coverage_pct:>9}%")
    print()
    print("  Per-prover breakdown:")
    for prover, count in sorted(prover_counts.items(), key=lambda x: -x[1]):
        print(f"    {prover:<20} {count:>10,}")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())
