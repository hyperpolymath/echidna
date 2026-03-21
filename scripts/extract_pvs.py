#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from NASA PVS library and convert to ECHIDNA training format.

Attempts to download from the NASA PVS library on GitHub. Falls back to
generating high-quality synthetic PVS proofs from standard theories.

PVS (Prototype Verification System) is a specification language and theorem
prover developed at SRI International, used extensively by NASA for
verifying flight-critical systems and air traffic management algorithms.

Output: training_data/proof_states_pvs.jsonl
ID range: 93000+
"""

import json
import os
import re
import urllib.request
import urllib.error
from typing import Dict, List, Any, Tuple

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTERNAL_DIR = os.path.join(REPO_ROOT, "external_corpora", "pvs")
OUTPUT_DIR = os.path.join(REPO_ROOT, "training_data")
OUTPUT_FILE = os.path.join(OUTPUT_DIR, "proof_states_pvs.jsonl")
STATS_FILE = os.path.join(OUTPUT_DIR, "stats_pvs.json")
START_ID = 93000

NASA_PVS_RAW = "https://raw.githubusercontent.com/nasa/pvslib/master"
NASA_PVS_FILES = [
    "reals/sq.pvs",
    "reals/abs_lems.pvs",
    "reals/real_fun_ops.pvs",
    "reals/sigma_nat.pvs",
    "structures/listn.pvs",
    "structures/set_as_list.pvs",
    "structures/sort_array.pvs",
    "algebra/group_def.pvs",
    "algebra/ring_def.pvs",
    "analysis/continuity_def.pvs",
    "analysis/derivative_def.pvs",
    "analysis/integral_def.pvs",
    "analysis/convergence_sequences.pvs",
    "topology/topology_def.pvs",
    "graphs/graph_def.pvs",
    "graphs/walks.pvs",
    "float/float.pvs",
    "float/ieee754_double.pvs",
    "ints/div_mod.pvs",
    "ints/gcd.pvs",
]


def parse_pvs_file(filepath: str) -> List[Dict[str, Any]]:
    """
    Parse a PVS .pvs file and extract LEMMA, THEOREM, and PROPOSITION forms.

    PVS declarations look like:
        theorem_name: THEOREM body
        lemma_name: LEMMA body
    """
    results = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
    except OSError:
        return results

    # Pattern: name : THEOREM|LEMMA|PROPOSITION body
    pattern = re.compile(
        r'(\w+)\s*:\s*(THEOREM|LEMMA|PROPOSITION|COROLLARY|AXIOM)\s+(.*?)(?=\n\s*\w+\s*:\s*(?:THEOREM|LEMMA|PROPOSITION|COROLLARY|AXIOM|TYPE|VAR|IMPORTING)|END\s+\w+|\Z)',
        re.DOTALL | re.IGNORECASE
    )

    for m in pattern.finditer(content):
        name = m.group(1).strip()
        kind = m.group(2).strip().upper()
        body = re.sub(r'\s+', ' ', m.group(3).strip())[:300]

        # Extract PVS proof strategy hints from body
        strategies = re.findall(r'\b(FORALL|EXISTS|IF|THEN|ELSE|AND|OR|NOT|IMPLIES|IFF|LAMBDA|LET|IN|WITH)\b', body, re.IGNORECASE)
        strategies_unique = list(dict.fromkeys(s.upper() for s in strategies))

        results.append({
            "theorem": name,
            "goal": body,
            "kind": kind,
            "tactics": strategies_unique,
            "source": f"pvs/{os.path.basename(filepath)}",
        })

    return results


def download_pvs_files() -> int:
    """Attempt to download NASA PVS library files."""
    downloaded = 0
    for rel_path in NASA_PVS_FILES:
        url = f"{NASA_PVS_RAW}/{rel_path}"
        local_path = os.path.join(EXTERNAL_DIR, os.path.basename(rel_path))
        if os.path.exists(local_path):
            downloaded += 1
            continue
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "ECHIDNA/1.5"})
            with urllib.request.urlopen(req, timeout=15) as resp:
                data = resp.read()
            with open(local_path, "wb") as fh:
                fh.write(data)
            downloaded += 1
            print(f"  Downloaded: {rel_path}")
        except (urllib.error.URLError, OSError, TimeoutError) as exc:
            print(f"  Skipped {rel_path}: {exc}")
    return downloaded


def generate_synthetic_pvs() -> List[Dict[str, Any]]:
    """
    Generate high-quality synthetic PVS proofs.

    PVS proof strategies include: (grind), (assert), (induct),
    (skolem!), (inst), (lemma), (expand), (lift-if), (prop),
    (typepred), (use), (replace).
    """
    real_analysis = [
        ("sq_nonneg", "FORALL (x: real): sq(x) >= 0", "(grind)"),
        ("sq_zero", "FORALL (x: real): sq(x) = 0 IFF x = 0", "(grind)"),
        ("abs_nonneg", "FORALL (x: real): abs(x) >= 0", "(grind)"),
        ("abs_zero", "FORALL (x: real): abs(x) = 0 IFF x = 0", "(grind)"),
        ("triangle_inequality", "FORALL (x, y: real): abs(x + y) <= abs(x) + abs(y)", "(grind)"),
        ("abs_mult", "FORALL (x, y: real): abs(x * y) = abs(x) * abs(y)", "(grind)"),
        ("sq_abs", "FORALL (x: real): sq(abs(x)) = sq(x)", "(grind)"),
        ("cauchy_schwarz_1d", "FORALL (x, y: real): sq(x * y) <= sq(x) * sq(y)", "(grind)"),
        ("mean_inequality", "FORALL (x, y: real): x >= 0 AND y >= 0 IMPLIES sq((x + y) / 2) >= x * y", "(grind)"),
        ("sqrt_sq", "FORALL (x: nonneg_real): sqrt(sq(x)) = x", "(grind)"),
        ("sq_sqrt", "FORALL (x: nonneg_real): sq(sqrt(x)) = x", "(grind)"),
        ("sqrt_mult", "FORALL (x, y: nonneg_real): sqrt(x * y) = sqrt(x) * sqrt(y)", "(grind)"),
        ("continuous_sum", "FORALL (f, g: [real -> real], a: real): continuous?(f, a) AND continuous?(g, a) IMPLIES continuous?(f + g, a)", "(grind)"),
        ("continuous_product", "FORALL (f, g: [real -> real], a: real): continuous?(f, a) AND continuous?(g, a) IMPLIES continuous?(f * g, a)", "(grind)"),
        ("ivt", "FORALL (f: [real -> real], a, b: real): a < b AND continuous_on?(f, closed_interval(a, b)) AND f(a) * f(b) < 0 IMPLIES EXISTS (c: real): a < c AND c < b AND f(c) = 0", "(skolem!) (inst?) (grind)"),
    ]

    integers = [
        ("div_mod_identity", "FORALL (a: int, b: posnat): a = b * div(a, b) + mod(a, b)", "(grind)"),
        ("mod_bounds", "FORALL (a: int, b: posnat): 0 <= mod(a, b) AND mod(a, b) < b", "(grind)"),
        ("gcd_comm", "FORALL (a, b: nat): gcd(a, b) = gcd(b, a)", "(induct \"a\") (grind)"),
        ("gcd_assoc", "FORALL (a, b, c: nat): gcd(gcd(a, b), c) = gcd(a, gcd(b, c))", "(induct \"a\") (grind)"),
        ("gcd_divides", "FORALL (a, b: nat): divides(gcd(a, b), a) AND divides(gcd(a, b), b)", "(induct \"a\") (grind)"),
        ("bezout", "FORALL (a, b: nat): EXISTS (x, y: int): gcd(a, b) = a * x + b * y", "(induct \"a\") (skolem!) (inst?) (grind)"),
        ("coprime_mult", "FORALL (a, b, c: nat): gcd(a, b) = 1 AND divides(a, b * c) IMPLIES divides(a, c)", "(lemma \"bezout\") (grind)"),
        ("prime_divides_product", "FORALL (p: posnat, a, b: nat): prime?(p) AND divides(p, a * b) IMPLIES divides(p, a) OR divides(p, b)", "(grind)"),
        ("infinitely_many_primes", "FORALL (n: nat): EXISTS (p: nat): p > n AND prime?(p)", "(skolem!) (inst?) (grind)"),
        ("fermat_little", "FORALL (a: int, p: posnat): prime?(p) AND NOT divides(p, a) IMPLIES mod(expt(a, p - 1), p) = 1", "(induct \"p\") (grind)"),
    ]

    sequences = [
        ("convergent_sum", "FORALL (s1, s2: sequence[real], L1, L2: real): convergent?(s1, L1) AND convergent?(s2, L2) IMPLIES convergent?(s1 + s2, L1 + L2)", "(skolem!) (inst?) (grind)"),
        ("convergent_product", "FORALL (s: sequence[real], L: real, c: real): convergent?(s, L) IMPLIES convergent?(c * s, c * L)", "(skolem!) (inst?) (grind)"),
        ("convergent_bounded", "FORALL (s: sequence[real], L: real): convergent?(s, L) IMPLIES bounded?(s)", "(skolem!) (inst?) (grind)"),
        ("squeeze_theorem", "FORALL (f, g, h: sequence[real], L: real): convergent?(f, L) AND convergent?(h, L) AND (FORALL (n: nat): f(n) <= g(n) AND g(n) <= h(n)) IMPLIES convergent?(g, L)", "(skolem!) (inst?) (grind)"),
        ("monotone_convergence", "FORALL (s: sequence[real]): monotone_increasing?(s) AND bounded_above?(s) IMPLIES convergent?(s)", "(use \"completeness_axiom\") (grind)"),
        ("cauchy_convergent", "FORALL (s: sequence[real]): cauchy?(s) IFF convergent?(s)", "(use \"completeness_axiom\") (grind)"),
        ("geometric_series", "FORALL (r: real): abs(r) < 1 IMPLIES convergent?(geometric(r), 1 / (1 - r))", "(induct-and-simplify)"),
        ("harmonic_diverges", "NOT convergent?(harmonic)", "(use \"comparison_test\") (grind)"),
    ]

    lists_structures = [
        ("length_append", "FORALL (l1, l2: list[T]): length(append(l1, l2)) = length(l1) + length(l2)", "(induct \"l1\") (grind)"),
        ("append_nil", "FORALL (l: list[T]): append(l, null) = l", "(induct \"l\") (grind)"),
        ("append_assoc", "FORALL (l1, l2, l3: list[T]): append(append(l1, l2), l3) = append(l1, append(l2, l3))", "(induct \"l1\") (grind)"),
        ("reverse_reverse", "FORALL (l: list[T]): reverse(reverse(l)) = l", "(induct \"l\") (grind)"),
        ("length_reverse", "FORALL (l: list[T]): length(reverse(l)) = length(l)", "(induct \"l\") (grind)"),
        ("member_append", "FORALL (x: T, l1, l2: list[T]): member(x, append(l1, l2)) IFF member(x, l1) OR member(x, l2)", "(induct \"l1\") (grind)"),
        ("nth_map", "FORALL (f: [T -> S], l: list[T], i: below[length(l)]): nth(map(f, l), i) = f(nth(l, i))", "(induct \"l\") (grind)"),
        ("length_map", "FORALL (f: [T -> S], l: list[T]): length(map(f, l)) = length(l)", "(induct \"l\") (grind)"),
        ("filter_append", "FORALL (P: pred[T], l1, l2: list[T]): filter(P, append(l1, l2)) = append(filter(P, l1), filter(P, l2))", "(induct \"l1\") (grind)"),
        ("sorted_append", "FORALL (l1, l2: list[real]): sorted?(l1) AND sorted?(l2) AND (FORALL (x: (l1), y: (l2)): x <= y) IMPLIES sorted?(append(l1, l2))", "(induct \"l1\") (grind)"),
    ]

    float_arithmetic = [
        ("float_add_comm", "FORALL (x, y: double): finite?(x) AND finite?(y) AND finite?(fadd(x, y)) IMPLIES fadd(x, y) = fadd(y, x)", "(grind)"),
        ("float_error_bound", "FORALL (x, y: double): finite?(x) AND finite?(y) AND finite?(fadd(x, y)) IMPLIES abs(fadd(x, y) - (FtoR(x) + FtoR(y))) <= ulp(fadd(x, y)) / 2", "(grind)"),
        ("float_mult_error", "FORALL (x, y: double): finite?(x) AND finite?(y) AND finite?(fmul(x, y)) IMPLIES abs(fmul(x, y) - FtoR(x) * FtoR(y)) <= ulp(fmul(x, y)) / 2", "(grind)"),
        ("sterbenz_lemma", "FORALL (x, y: double): finite?(x) AND finite?(y) AND y / 2 <= x AND x <= 2 * y IMPLIES finite?(fsub(x, y)) AND fsub(x, y) = FtoR(x) - FtoR(y)", "(grind)"),
        ("float_sqrt_correct", "FORALL (x: double): finite?(x) AND FtoR(x) >= 0 IMPLIES abs(fsqrt(x) - sqrt(FtoR(x))) <= ulp(fsqrt(x)) / 2", "(grind)"),
    ]

    graphs = [
        ("walk_length", "FORALL (G: graph[T], w: Walk(G)): length(edges(w)) = length(vertices(w)) - 1", "(induct \"w\") (grind)"),
        ("path_is_walk", "FORALL (G: graph[T], p: Path(G)): walk?(G, p)", "(grind)"),
        ("connected_symmetric", "FORALL (G: graph[T], u, v: (vert(G))): connected?(G, u, v) IMPLIES connected?(G, v, u)", "(use \"reverse_walk\") (grind)"),
        ("tree_edges", "FORALL (G: graph[T]): tree?(G) IMPLIES card(edges(G)) = card(vert(G)) - 1", "(induct-on-structure) (grind)"),
        ("euler_formula", "FORALL (G: graph[T]): connected?(G) AND planar?(G) IMPLIES card(vert(G)) - card(edges(G)) + card(faces(G)) = 2", "(induct-on-structure) (grind)"),
    ]

    all_categories = [
        ("real_analysis", real_analysis),
        ("integers", integers),
        ("sequences", sequences),
        ("lists_structures", lists_structures),
        ("float_arithmetic", float_arithmetic),
        ("graphs", graphs),
    ]

    proofs = []
    for category, theorems in all_categories:
        for name, goal, strategy in theorems:
            strat_names = re.findall(r'\((\w[\w-]*)', strategy)
            proofs.append({
                "theorem": name,
                "goal": f"{name}: LEMMA {goal}",
                "tactic_proof": strategy,
                "tactics": list(dict.fromkeys(strat_names))[:20],
                "source": f"pvs_synthetic/{category}",
            })
    return proofs


def run() -> Tuple[int, int]:
    """Run the full extraction pipeline."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(EXTERNAL_DIR, exist_ok=True)

    all_entries: List[Dict[str, Any]] = []
    extracted_count = 0

    print("[PVS] Phase 1: Attempting to download NASA PVS library ...")
    downloaded = download_pvs_files()
    print(f"  Downloaded/cached {downloaded} files")

    for fname in os.listdir(EXTERNAL_DIR):
        if fname.endswith(".pvs"):
            fpath = os.path.join(EXTERNAL_DIR, fname)
            parsed = parse_pvs_file(fpath)
            for entry in parsed:
                all_entries.append(entry)
            if parsed:
                print(f"  Parsed {len(parsed)} theorems from {fname}")
    extracted_count = len(all_entries)

    print(f"[PVS] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_pvs()
    existing_names = {e["theorem"] for e in all_entries}
    added = 0
    for entry in synthetic:
        if entry["theorem"] not in existing_names:
            all_entries.append(entry)
            existing_names.add(entry["theorem"])
            added += 1
    print(f"  Generated {added} unique synthetic proofs")

    current_id = START_ID
    output_records = []
    for entry in all_entries:
        record = {
            "id": current_id,
            "prover": "PVS",
            "theorem": entry["theorem"],
            "goal": entry["goal"],
            "context": entry.get("tactics", []),
            "tactic_proof": entry.get("tactic_proof", ""),
            "source": entry.get("source", "pvs"),
        }
        output_records.append(record)
        current_id += 1

    with open(OUTPUT_FILE, "w", encoding="utf-8") as fh:
        for rec in output_records:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    stats = {
        "prover": "PVS",
        "total_proofs": len(output_records),
        "extracted_from_source": extracted_count,
        "synthetic_added": len(output_records) - extracted_count,
        "id_range": [START_ID, current_id - 1],
        "output_file": OUTPUT_FILE,
    }
    with open(STATS_FILE, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2)

    print(f"\n[PVS] COMPLETE: {len(output_records)} proofs written to {OUTPUT_FILE}")
    print(f"  Extracted from source: {extracted_count}")
    print(f"  Synthetic: {len(output_records) - extracted_count}")
    return extracted_count, len(output_records) - extracted_count


if __name__ == "__main__":
    run()
