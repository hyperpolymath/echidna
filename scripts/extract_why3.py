#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from Why3 examples and convert to ECHIDNA training format.

Attempts to download from the Why3 GitLab repository (examples/ dir).
Falls back to generating high-quality synthetic Why3 proofs.

Why3 is a platform for deductive program verification, featuring a rich
specification language (WhyML) and integration with many automated and
interactive provers.

Output: training_data/proof_states_why3.jsonl
ID range: 95000+
"""

import json
import os
import re
import urllib.request
import urllib.error
from typing import Dict, List, Any, Tuple

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTERNAL_DIR = os.path.join(REPO_ROOT, "external_corpora", "why3")
OUTPUT_DIR = os.path.join(REPO_ROOT, "training_data")
OUTPUT_FILE = os.path.join(OUTPUT_DIR, "proof_states_why3.jsonl")
STATS_FILE = os.path.join(OUTPUT_DIR, "stats_why3.json")
START_ID = 95000

WHY3_RAW = "https://gitlab.inria.fr/why3/why3/-/raw/master"
WHY3_FILES = [
    "examples/euler001.mlw",
    "examples/fibonacci.mlw",
    "examples/insertion_sort.mlw",
    "examples/selection_sort.mlw",
    "examples/mergesort_list.mlw",
    "examples/binary_search.mlw",
    "examples/queens.mlw",
    "examples/power.mlw",
    "examples/factorial.mlw",
    "examples/gcd.mlw",
    "examples/maximum_subarray.mlw",
    "examples/knuth_prime_numbers.mlw",
    "examples/dutch_flag.mlw",
    "examples/ring_buffer.mlw",
    "examples/tortoise_and_hare.mlw",
    "examples/same_fringe.mlw",
]


def parse_why3_file(filepath: str) -> List[Dict[str, Any]]:
    """
    Parse a Why3 .mlw file and extract lemma/goal/predicate patterns.

    Why3 files contain modules with:
        lemma name: formula
        goal name: formula
        let rec function ... = ... ensures { ... }
    """
    results = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
    except OSError:
        return results

    # Extract lemma/goal declarations
    pattern = re.compile(
        r'(lemma|goal|axiom)\s+(\w+)\s*:\s*(.*?)(?=\n\s*(?:lemma|goal|axiom|let|val|predicate|function|end|use|module)|\Z)',
        re.DOTALL | re.IGNORECASE
    )
    for m in pattern.finditer(content):
        kind = m.group(1).strip()
        name = m.group(2).strip()
        body = re.sub(r'\s+', ' ', m.group(3).strip())[:300]
        keywords = re.findall(r'\b(forall|exists|ensures|requires|invariant|variant|raises|reads|writes|diverges)\b', body, re.IGNORECASE)
        results.append({
            "theorem": name,
            "goal": body,
            "kind": kind,
            "tactics": list(dict.fromkeys(k.lower() for k in keywords)),
            "source": f"why3/{os.path.basename(filepath)}",
        })

    # Extract function specs (ensures/requires)
    func_pattern = re.compile(
        r'let\s+(?:rec\s+)?(\w+).*?(?:requires\s*\{(.*?)\})?.*?(?:ensures\s*\{(.*?)\})',
        re.DOTALL
    )
    for m in func_pattern.finditer(content):
        name = m.group(1)
        requires = m.group(2)
        ensures = m.group(3)
        if ensures:
            ensures_clean = re.sub(r'\s+', ' ', ensures.strip())[:200]
            results.append({
                "theorem": f"{name}_spec",
                "goal": f"ensures {{ {ensures_clean} }}",
                "kind": "function_spec",
                "tactics": ["ensures", "requires"] if requires else ["ensures"],
                "source": f"why3/{os.path.basename(filepath)}",
            })

    return results


def download_why3_files() -> int:
    """Attempt to download Why3 example files."""
    downloaded = 0
    for rel_path in WHY3_FILES:
        url = f"{WHY3_RAW}/{rel_path}"
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


def generate_synthetic_why3() -> List[Dict[str, Any]]:
    """
    Generate high-quality synthetic Why3 proofs using WhyML syntax.
    """
    arithmetic = [
        ("add_comm", "forall x y: int. x + y = y + x", ""),
        ("add_assoc", "forall x y z: int. (x + y) + z = x + (y + z)", ""),
        ("mul_comm", "forall x y: int. x * y = y * x", ""),
        ("mul_assoc", "forall x y z: int. (x * y) * z = x * (y * z)", ""),
        ("distrib_left", "forall x y z: int. x * (y + z) = x * y + x * z", ""),
        ("add_zero", "forall x: int. x + 0 = x", ""),
        ("mul_one", "forall x: int. x * 1 = x", ""),
        ("mul_zero", "forall x: int. x * 0 = 0", ""),
        ("sub_self", "forall x: int. x - x = 0", ""),
        ("neg_neg", "forall x: int. -(-x) = x", ""),
        ("abs_nonneg", "forall x: int. abs x >= 0", ""),
        ("abs_pos", "forall x: int. x > 0 -> abs x = x", ""),
        ("abs_neg", "forall x: int. x < 0 -> abs x = -x", ""),
        ("div_mod", "forall a b: int. b <> 0 -> a = b * div a b + mod a b", ""),
        ("mod_bounds", "forall a: int, b: int. b > 0 -> 0 <= mod a b < b", ""),
    ]

    sorting = [
        ("insertion_sort_sorted", "forall a: array int. let b = insertion_sort a in sorted b", "ensures { sorted result } ensures { permut_all (old a) result }"),
        ("insertion_sort_permut", "forall a: array int. let b = insertion_sort a in permut_all a b", "ensures { permut_all (old a) result }"),
        ("selection_sort_sorted", "forall a: array int. let b = selection_sort a in sorted b", "ensures { sorted result }"),
        ("merge_sorted", "forall l1 l2: list int. sorted_list l1 -> sorted_list l2 -> sorted_list (merge l1 l2)", ""),
        ("merge_permut", "forall l1 l2: list int. permut (merge l1 l2) (l1 ++ l2)", ""),
        ("mergesort_sorted", "forall l: list int. sorted_list (mergesort l)", "ensures { sorted_list result }"),
        ("mergesort_permut", "forall l: list int. permut (mergesort l) l", "ensures { permut result l }"),
        ("binary_search_found", "forall a: array int, v: int. sorted a -> (exists i. 0 <= i < length a /\\ a[i] = v) -> let r = binary_search a v in 0 <= r < length a /\\ a[r] = v", "ensures { 0 <= result < length a } ensures { a[result] = v }"),
        ("binary_search_not_found", "forall a: array int, v: int. sorted a -> (forall i. 0 <= i < length a -> a[i] <> v) -> binary_search a v = -1", "ensures { result = -1 }"),
        ("partition_spec", "forall a: array int, lo hi: int. lo <= hi -> let (a', p) = partition a lo hi in lo <= p <= hi /\\ (forall i. lo <= i < p -> a'[i] <= a'[p]) /\\ (forall i. p < i <= hi -> a'[i] >= a'[p])", ""),
    ]

    data_structures = [
        ("list_append_nil", "forall l: list 'a. l ++ Nil = l", ""),
        ("list_append_assoc", "forall l1 l2 l3: list 'a. (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)", ""),
        ("list_length_append", "forall l1 l2: list 'a. length (l1 ++ l2) = length l1 + length l2", ""),
        ("list_reverse_reverse", "forall l: list 'a. reverse (reverse l) = l", ""),
        ("list_length_reverse", "forall l: list 'a. length (reverse l) = length l", ""),
        ("list_mem_append", "forall x: 'a, l1 l2: list 'a. mem x (l1 ++ l2) <-> mem x l1 \\/ mem x l2", ""),
        ("list_map_length", "forall f: 'a -> 'b, l: list 'a. length (map f l) = length l", ""),
        ("list_map_compose", "forall f: 'b -> 'c, g: 'a -> 'b, l: list 'a. map f (map g l) = map (fun x -> f (g x)) l", ""),
        ("queue_fifo", "forall q: queue 'a, x: 'a. let q' = push q x in peek (q') = if is_empty q then x else peek q", ""),
        ("stack_lifo", "forall s: stack 'a, x: 'a. peek (push s x) = x", ""),
    ]

    program_verification = [
        ("loop_invariant_sum", "let sum (a: array int) (n: int) : int requires { n = length a } ensures { result = sum_func a 0 n } = let ref s = 0 in for i = 0 to n - 1 do invariant { s = sum_func a 0 i } s <- s + a[i] done; s",
         "requires { n = length a } ensures { result = sum_func a 0 n } invariant { s = sum_func a 0 i }"),
        ("factorial_correct", "let rec factorial (n: int) : int requires { n >= 0 } ensures { result = fact n } variant { n } = if n = 0 then 1 else n * factorial (n - 1)",
         "requires { n >= 0 } ensures { result = fact n } variant { n }"),
        ("fibonacci_correct", "let rec fib (n: int) : int requires { n >= 0 } ensures { result = fibonacci n } variant { n } = if n <= 1 then n else fib (n - 1) + fib (n - 2)",
         "requires { n >= 0 } ensures { result = fibonacci n } variant { n }"),
        ("gcd_correct", "let rec gcd (a b: int) : int requires { a >= 0 /\\ b >= 0 } ensures { result = Gcd.gcd a b } variant { b } = if b = 0 then a else gcd b (mod a b)",
         "requires { a >= 0 /\\ b >= 0 } ensures { result = Gcd.gcd a b } variant { b }"),
        ("power_correct", "let rec power (x n: int) : int requires { n >= 0 } ensures { result = pow x n } variant { n } = if n = 0 then 1 else if mod n 2 = 0 then let p = power x (div n 2) in p * p else x * power x (n - 1)",
         "requires { n >= 0 } ensures { result = pow x n } variant { n }"),
        ("max_correct", "let max (a b: int) : int ensures { result >= a /\\ result >= b } ensures { result = a \\/ result = b } = if a >= b then a else b",
         "ensures { result >= a /\\ result >= b } ensures { result = a \\/ result = b }"),
        ("swap_correct", "let swap (a: array 'a) (i j: int) : unit requires { 0 <= i < length a /\\ 0 <= j < length a } ensures { a[i] = old a[j] /\\ a[j] = old a[i] } ensures { forall k. k <> i -> k <> j -> a[k] = old a[k] }",
         "requires { 0 <= i < length a /\\ 0 <= j < length a } ensures { a[i] = old a[j] /\\ a[j] = old a[i] }"),
        ("dutch_flag", "let dutch_flag (a: array color) : unit ensures { sorted_colors a } ensures { permut_all (old a) a } = let ref r = 0 in let ref w = 0 in let ref b = length a - 1 in while w <= b do invariant { ... } variant { b - w + 1 } ... done",
         "ensures { sorted_colors result } ensures { permut_all (old a) a } invariant { ... } variant { b - w + 1 }"),
        ("ring_buffer_push", "let push (rb: ring_buffer 'a) (x: 'a) : unit requires { not is_full rb } ensures { length rb = old (length rb) + 1 }",
         "requires { not is_full rb } ensures { length rb = old (length rb) + 1 }"),
        ("ring_buffer_pop", "let pop (rb: ring_buffer 'a) : 'a requires { not is_empty rb } ensures { length rb = old (length rb) - 1 }",
         "requires { not is_empty rb } ensures { length rb = old (length rb) - 1 }"),
    ]

    graph_algorithms = [
        ("dfs_visited", "forall g: graph, s: vertex. let v = dfs g s in forall u: vertex. mem u v <-> reachable g s u", "ensures { forall u. mem u result <-> reachable g s u }"),
        ("bfs_shortest", "forall g: graph, s: vertex. let d = bfs g s in forall u: vertex. d[u] = shortest_path g s u", "ensures { forall u. result[u] = shortest_path g s u }"),
        ("dijkstra_correct", "forall g: weighted_graph, s: vertex. let d = dijkstra g s in forall u: vertex. d[u] = shortest_weighted_path g s u", "ensures { forall u. result[u] = shortest_weighted_path g s u }"),
        ("topological_sort_valid", "forall g: dag. let l = topological_sort g in forall (u v: vertex). edge g u v -> index l u < index l v", "ensures { forall u v. edge g u v -> index result u < index result v }"),
        ("mst_correct", "forall g: connected_weighted_graph. let t = kruskal g in is_spanning_tree t g /\\ weight t = min_spanning_weight g", "ensures { is_spanning_tree result g } ensures { weight result = min_spanning_weight g }"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("sorting", sorting),
        ("data_structures", data_structures),
        ("program_verification", program_verification),
        ("graph_algorithms", graph_algorithms),
    ]

    proofs = []
    for category, theorems in all_categories:
        for entry in theorems:
            name, goal = entry[0], entry[1]
            spec = entry[2] if len(entry) > 2 else ""
            keywords = re.findall(r'\b(forall|exists|ensures|requires|invariant|variant|raises|sorted|permut|mem|length)\b', goal + " " + spec, re.IGNORECASE)
            proofs.append({
                "theorem": name,
                "goal": goal,
                "tactic_proof": spec,
                "tactics": list(dict.fromkeys(k.lower() for k in keywords))[:20],
                "source": f"why3_synthetic/{category}",
            })
    return proofs


def run() -> Tuple[int, int]:
    """Run the full extraction pipeline."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(EXTERNAL_DIR, exist_ok=True)

    all_entries: List[Dict[str, Any]] = []
    extracted_count = 0

    print("[Why3] Phase 1: Attempting to download from GitLab ...")
    downloaded = download_why3_files()
    print(f"  Downloaded/cached {downloaded} files")

    for fname in os.listdir(EXTERNAL_DIR):
        if fname.endswith(".mlw"):
            fpath = os.path.join(EXTERNAL_DIR, fname)
            parsed = parse_why3_file(fpath)
            for entry in parsed:
                all_entries.append(entry)
            if parsed:
                print(f"  Parsed {len(parsed)} theorems from {fname}")
    extracted_count = len(all_entries)

    print(f"[Why3] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_why3()
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
            "prover": "Why3",
            "theorem": entry["theorem"],
            "goal": entry["goal"],
            "context": entry.get("tactics", []),
            "tactic_proof": entry.get("tactic_proof", ""),
            "source": entry.get("source", "why3"),
        }
        output_records.append(record)
        current_id += 1

    with open(OUTPUT_FILE, "w", encoding="utf-8") as fh:
        for rec in output_records:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    stats = {
        "prover": "Why3",
        "total_proofs": len(output_records),
        "extracted_from_source": extracted_count,
        "synthetic_added": len(output_records) - extracted_count,
        "id_range": [START_ID, current_id - 1],
        "output_file": OUTPUT_FILE,
    }
    with open(STATS_FILE, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2)

    print(f"\n[Why3] COMPLETE: {len(output_records)} proofs written to {OUTPUT_FILE}")
    print(f"  Extracted from source: {extracted_count}")
    print(f"  Synthetic: {len(output_records) - extracted_count}")
    return extracted_count, len(output_records) - extracted_count


if __name__ == "__main__":
    run()
