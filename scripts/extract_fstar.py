#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from F* (Project Everest) and convert to ECHIDNA training format.

Attempts to download from the F* GitHub repository (examples/ dir). Falls back
to generating high-quality synthetic F* proofs.

F* is a general-purpose ML-like functional programming language with effects
aimed at program verification. It is used in Project Everest for verified
cryptographic libraries (HACL*, EverCrypt, miTLS).

Output: training_data/proof_states_fstar.jsonl
ID range: 97000+
"""

import json
import os
import re
import urllib.request
import urllib.error
from typing import Dict, List, Any, Tuple

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTERNAL_DIR = os.path.join(REPO_ROOT, "external_corpora", "fstar")
OUTPUT_DIR = os.path.join(REPO_ROOT, "training_data")
OUTPUT_FILE = os.path.join(OUTPUT_DIR, "proof_states_fstar.jsonl")
STATS_FILE = os.path.join(OUTPUT_DIR, "stats_fstar.json")
START_ID = 97000

FSTAR_RAW = "https://raw.githubusercontent.com/FStarLang/FStar/master"
FSTAR_FILES = [
    "examples/algorithms/BinarySearch.fst",
    "examples/algorithms/InsertionSort.fst",
    "examples/algorithms/QuickSort.fst",
    "examples/algorithms/MergeSort.fst",
    "examples/data_structures/BinomialQueue.fst",
    "examples/data_structures/RBTree.fst",
    "examples/crypto/Hacl.fst",
    "examples/micro-benchmarks/Arith.fst",
    "examples/micro-benchmarks/Nat.fst",
    "examples/termination/Ackermann.fst",
    "examples/termination/Fibonacci.fst",
    "ulib/FStar.List.Tot.fst",
    "ulib/FStar.Seq.Base.fst",
    "ulib/FStar.Math.Lemmas.fst",
]


def parse_fstar_file(filepath: str) -> List[Dict[str, Any]]:
    """Parse an F* .fst file and extract val/let definitions with specs."""
    results = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
    except OSError:
        return results

    # val declarations with refinement types
    val_pattern = re.compile(
        r'val\s+(\w+)\s*:\s*(.*?)(?=\nval\s|\nlet\s|\ntype\s|\nopen\s|\nmodule\s|\Z)',
        re.DOTALL
    )
    for m in val_pattern.finditer(content):
        name = m.group(1).strip()
        sig = re.sub(r'\s+', ' ', m.group(2).strip())[:400]
        if not sig or len(sig) < 5:
            continue
        keywords = re.findall(r'\b(Tot|Lemma|Pure|ST|Stack|GTot|requires|ensures|decreases|modifies)\b', sig)
        results.append({
            "theorem": name,
            "goal": sig,
            "tactics": list(dict.fromkeys(keywords))[:20],
            "source": f"fstar/{os.path.basename(filepath)}",
        })

    # let with refinement types or Lemma
    let_pattern = re.compile(
        r'let\s+(?:rec\s+)?(\w+)\s*(?::.*?)?\s*=\s*(.*?)(?=\nlet\s|\nval\s|\ntype\s|\Z)',
        re.DOTALL
    )
    for m in let_pattern.finditer(content):
        name = m.group(1).strip()
        body = re.sub(r'\s+', ' ', m.group(2).strip())[:300]
        if 'Lemma' in body or 'assert' in body or 'calc' in body:
            keywords = re.findall(r'\b(Lemma|assert|calc|assume|admit|Classical)\b', body)
            results.append({
                "theorem": f"{name}_impl",
                "goal": body[:200],
                "tactics": list(dict.fromkeys(keywords))[:20],
                "source": f"fstar/{os.path.basename(filepath)}",
            })

    return results


def download_fstar_files() -> int:
    """Attempt to download F* source files."""
    downloaded = 0
    for rel_path in FSTAR_FILES:
        url = f"{FSTAR_RAW}/{rel_path}"
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


def generate_synthetic_fstar() -> List[Dict[str, Any]]:
    """Generate high-quality synthetic F* proofs."""

    arithmetic = [
        ("add_comm", "val add_comm: a:int -> b:int -> Lemma (a + b == b + a)", "let add_comm a b = ()"),
        ("add_assoc", "val add_assoc: a:int -> b:int -> c:int -> Lemma ((a + b) + c == a + (b + c))", "let add_assoc a b c = ()"),
        ("mul_comm", "val mul_comm: a:int -> b:int -> Lemma (a * b == b * a)", "let mul_comm a b = ()"),
        ("mul_assoc", "val mul_assoc: a:int -> b:int -> c:int -> Lemma ((a * b) * c == a * (b * c))", "let mul_assoc a b c = ()"),
        ("distributive", "val distributive: a:int -> b:int -> c:int -> Lemma (a * (b + c) == a * b + a * c)", "let distributive a b c = ()"),
        ("add_zero_r", "val add_zero_r: a:int -> Lemma (a + 0 == a)", "let add_zero_r a = ()"),
        ("mul_one_r", "val mul_one_r: a:int -> Lemma (a * 1 == a)", "let mul_one_r a = ()"),
        ("mul_zero_r", "val mul_zero_r: a:int -> Lemma (a * 0 == 0)", "let mul_zero_r a = ()"),
        ("pow_add", "val pow_add: b:nat -> m:nat -> n:nat -> Lemma (ensures pow b (m + n) == pow b m * pow b n) (decreases m)", "let rec pow_add b m n = if m = 0 then () else pow_add b (m - 1) n"),
        ("pow_mul", "val pow_mul: b:nat -> m:nat -> n:nat -> Lemma (ensures pow b (m * n) == pow (pow b m) n) (decreases n)", "let rec pow_mul b m n = if n = 0 then () else (pow_add b m (m * (n - 1)); pow_mul b m (n - 1))"),
        ("mod_add", "val mod_add: a:int -> b:int -> n:pos -> Lemma ((a + b) % n == ((a % n) + (b % n)) % n)", "let mod_add a b n = FStar.Math.Lemmas.lemma_mod_plus_distr_l a b n"),
        ("div_exact", "val div_exact: a:nat -> b:pos -> Lemma (requires a % b == 0) (ensures a / b * b == a)", "let div_exact a b = FStar.Math.Lemmas.lemma_div_exact a b"),
    ]

    lists = [
        ("append_nil", "val append_nil: #a:Type -> l:list a -> Lemma (l @ [] == l)", "let rec append_nil #a l = match l with | [] -> () | _::tl -> append_nil tl"),
        ("append_assoc", "val append_assoc: #a:Type -> l1:list a -> l2:list a -> l3:list a -> Lemma ((l1 @ l2) @ l3 == l1 @ (l2 @ l3))", "let rec append_assoc #a l1 l2 l3 = match l1 with | [] -> () | _::tl -> append_assoc tl l2 l3"),
        ("length_append", "val length_append: #a:Type -> l1:list a -> l2:list a -> Lemma (length (l1 @ l2) == length l1 + length l2)", "let rec length_append #a l1 l2 = match l1 with | [] -> () | _::tl -> length_append tl l2"),
        ("rev_rev", "val rev_rev: #a:Type -> l:list a -> Lemma (rev (rev l) == l)", "let rec rev_rev #a l = match l with | [] -> () | hd::tl -> rev_append_rev tl [hd]; rev_rev tl"),
        ("map_append", "val map_append: #a:Type -> #b:Type -> f:(a -> b) -> l1:list a -> l2:list a -> Lemma (map f (l1 @ l2) == map f l1 @ map f l2)", "let rec map_append #a #b f l1 l2 = match l1 with | [] -> () | _::tl -> map_append f tl l2"),
        ("length_map", "val length_map: #a:Type -> #b:Type -> f:(a -> b) -> l:list a -> Lemma (length (map f l) == length l)", "let rec length_map #a #b f l = match l with | [] -> () | _::tl -> length_map f tl"),
        ("mem_append", "val mem_append: #a:eqtype -> x:a -> l1:list a -> l2:list a -> Lemma (mem x (l1 @ l2) <==> mem x l1 || mem x l2)", "let rec mem_append #a x l1 l2 = match l1 with | [] -> () | _::tl -> mem_append x tl l2"),
        ("filter_append", "val filter_append: #a:Type -> f:(a -> bool) -> l1:list a -> l2:list a -> Lemma (filter f (l1 @ l2) == filter f l1 @ filter f l2)", "let rec filter_append #a f l1 l2 = match l1 with | [] -> () | hd::tl -> filter_append f tl l2"),
        ("fold_left_append", "val fold_left_append: #a:Type -> #b:Type -> f:(b -> a -> b) -> init:b -> l1:list a -> l2:list a -> Lemma (fold_left f init (l1 @ l2) == fold_left f (fold_left f init l1) l2)", "let rec fold_left_append #a #b f init l1 l2 = match l1 with | [] -> () | hd::tl -> fold_left_append f (f init hd) tl l2"),
        ("for_all_append", "val for_all_append: #a:Type -> f:(a -> bool) -> l1:list a -> l2:list a -> Lemma (for_all f (l1 @ l2) <==> for_all f l1 && for_all f l2)", "let rec for_all_append #a f l1 l2 = match l1 with | [] -> () | _::tl -> for_all_append f tl l2"),
    ]

    crypto_verification = [
        ("aead_encrypt_decrypt", "val aead_encrypt_decrypt: k:key -> n:nonce -> p:plaintext -> ad:aad -> Lemma (ensures (let c = aead_encrypt k n p ad in aead_decrypt k n c ad == Some p))", ""),
        ("hmac_verify", "val hmac_verify: k:key -> m:msg -> t:tag -> Lemma (requires t == hmac k m) (ensures verify_hmac k m t == true)", ""),
        ("hash_collision_resistance", "val hash_collision_resistance: m1:msg -> m2:msg -> Lemma (requires m1 <> m2) (ensures hash m1 <> hash m2) [SMTPat (hash m1); SMTPat (hash m2)]", ""),
        ("kdf_extract_length", "val kdf_extract_length: salt:bytes -> ikm:bytes -> Lemma (ensures length (kdf_extract salt ikm) == hash_length)", ""),
        ("chacha20_involutive", "val chacha20_involutive: k:key -> n:nonce -> ctr:nat -> p:bytes -> Lemma (ensures chacha20 k n ctr (chacha20 k n ctr p) == p)", ""),
    ]

    effects_and_state = [
        ("incr_spec", "val incr: r:ref int -> ST unit (requires fun h -> True) (ensures fun h0 _ h1 -> sel h1 r == sel h0 r + 1)", "let incr r = r := !r + 1"),
        ("swap_spec", "val swap: r1:ref int -> r2:ref int -> ST unit (requires fun h -> True) (ensures fun h0 _ h1 -> sel h1 r1 == sel h0 r2 /\\ sel h1 r2 == sel h0 r1)", "let swap r1 r2 = let t = !r1 in r1 := !r2; r2 := t"),
        ("factorial_spec", "val factorial: n:nat -> Tot (r:nat{r >= 1})", "let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)"),
        ("fibonacci_spec", "val fibonacci: n:nat -> Tot nat (decreases n)", "let rec fibonacci n = if n <= 1 then n else fibonacci (n - 1) + fibonacci (n - 2)"),
        ("alloc_and_free", "val alloc_and_free: n:nat -> ST unit (requires fun h -> True) (ensures fun h0 _ h1 -> modifies Set.empty h0 h1)", "let alloc_and_free n = let r = alloc n in free r"),
    ]

    refinement_types = [
        ("nat_positive", "val nat_positive: n:nat{n > 0} -> Tot (r:nat{r >= 0})", "let nat_positive n = n - 1"),
        ("bounded_add", "val bounded_add: a:nat{a < 100} -> b:nat{b < 100} -> Tot (r:nat{r < 200})", "let bounded_add a b = a + b"),
        ("safe_div", "val safe_div: a:int -> b:int{b <> 0} -> Tot int", "let safe_div a b = a / b"),
        ("vector_index", "val vector_index: #n:nat -> v:vector n -> i:nat{i < n} -> Tot elem", "let vector_index #n v i = Seq.index v i"),
        ("sorted_insert", "val sorted_insert: x:int -> l:list int{sorted l} -> Tot (r:list int{sorted r /\\ length r == length l + 1})", ""),
        ("non_empty_head", "val non_empty_head: #a:Type -> l:list a{Cons? l} -> Tot a", "let non_empty_head #a l = match l with | hd::_ -> hd"),
        ("matrix_mult_dims", "val matrix_mult: #m:nat -> #n:nat -> #p:nat -> matrix m n -> matrix n p -> Tot (matrix m p)", ""),
        ("well_typed_eval", "val well_typed_eval: #t:typ -> e:exp{has_type e t} -> Tot (v:value{value_type v t})", ""),
    ]

    termination = [
        ("ackermann", "val ackermann: m:nat -> n:nat -> Tot nat (decreases %[m; n])", "let rec ackermann m n = if m = 0 then n + 1 else if n = 0 then ackermann (m - 1) 1 else ackermann (m - 1) (ackermann m (n - 1))"),
        ("gcd_termination", "val gcd: a:nat -> b:nat{a > 0 || b > 0} -> Tot (r:pos) (decreases b)", "let rec gcd a b = if b = 0 then a else gcd b (a % b)"),
        ("collatz_steps", "val collatz_steps: n:pos -> Tot nat (decreases %[n; if n = 1 then 0 else 1])", ""),
        ("mutual_even", "val mutual_even: n:nat -> Tot bool (decreases n)\nval mutual_odd: n:nat -> Tot bool (decreases n)", "let rec mutual_even n = if n = 0 then true else mutual_odd (n - 1)\nand mutual_odd n = if n = 0 then false else mutual_even (n - 1)"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("lists", lists),
        ("crypto", crypto_verification),
        ("effects", effects_and_state),
        ("refinement", refinement_types),
        ("termination", termination),
    ]

    proofs = []
    for category, entries in all_categories:
        for entry in entries:
            name = entry[0]
            sig = entry[1]
            impl = entry[2] if len(entry) > 2 else ""

            keywords = re.findall(r'\b(Lemma|Tot|Pure|ST|GTot|requires|ensures|decreases|modifies|SMTPat)\b', sig)
            proofs.append({
                "theorem": name,
                "goal": sig,
                "tactic_proof": impl,
                "tactics": list(dict.fromkeys(keywords))[:20],
                "source": f"fstar_synthetic/{category}",
            })
    return proofs


def run() -> Tuple[int, int]:
    """Run the full extraction pipeline."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(EXTERNAL_DIR, exist_ok=True)

    all_entries: List[Dict[str, Any]] = []
    extracted_count = 0

    print("[F*] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_fstar_files()
    print(f"  Downloaded/cached {downloaded} files")

    for fname in os.listdir(EXTERNAL_DIR):
        if fname.endswith(".fst"):
            fpath = os.path.join(EXTERNAL_DIR, fname)
            parsed = parse_fstar_file(fpath)
            for entry in parsed:
                all_entries.append(entry)
            if parsed:
                print(f"  Parsed {len(parsed)} from {fname}")
    extracted_count = len(all_entries)

    print(f"[F*] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_fstar()
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
            "prover": "FStar",
            "theorem": entry["theorem"],
            "goal": entry["goal"],
            "context": entry.get("tactics", []),
            "tactic_proof": entry.get("tactic_proof", ""),
            "source": entry.get("source", "fstar"),
        }
        output_records.append(record)
        current_id += 1

    with open(OUTPUT_FILE, "w", encoding="utf-8") as fh:
        for rec in output_records:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    stats = {
        "prover": "FStar",
        "total_proofs": len(output_records),
        "extracted_from_source": extracted_count,
        "synthetic_added": len(output_records) - extracted_count,
        "id_range": [START_ID, current_id - 1],
    }
    with open(STATS_FILE, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2)

    print(f"\n[F*] COMPLETE: {len(output_records)} proofs written to {OUTPUT_FILE}")
    return extracted_count, len(output_records) - extracted_count


if __name__ == "__main__":
    run()
