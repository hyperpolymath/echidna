#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from ACL2 community books and convert to ECHIDNA training format.

Attempts to download from the ACL2 GitHub repository (books/ directory).
Falls back to generating high-quality synthetic ACL2 proofs from standard
patterns (defthm, defun, verify-guards).

ACL2 (A Computational Logic for Applicative Common Lisp) is an industrial-
strength theorem prover used for hardware and software verification (e.g.
AMD floating-point division, JVM bytecode verification).

Output: training_data/proof_states_acl2.jsonl
ID range: 92000+
"""

import json
import os
import re
import urllib.request
import urllib.error
from typing import Dict, List, Any, Tuple

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTERNAL_DIR = os.path.join(REPO_ROOT, "external_corpora", "acl2")
OUTPUT_DIR = os.path.join(REPO_ROOT, "training_data")
OUTPUT_FILE = os.path.join(OUTPUT_DIR, "proof_states_acl2.jsonl")
STATS_FILE = os.path.join(OUTPUT_DIR, "stats_acl2.json")
START_ID = 92000

ACL2_RAW_BASE = "https://raw.githubusercontent.com/acl2/acl2/master"
ACL2_FILES = [
    "books/arithmetic/top.lisp",
    "books/arithmetic-5/top.lisp",
    "books/std/lists/top.lisp",
    "books/std/lists/append.lisp",
    "books/std/lists/rev.lisp",
    "books/std/lists/nth.lisp",
    "books/std/lists/len.lisp",
    "books/std/alists/top.lisp",
    "books/ihs/ihs-definitions.lisp",
    "books/ihs/logops-lemmas.lisp",
    "books/data-structures/list-theory.lisp",
    "books/sorting/msort.lisp",
    "books/sorting/isort.lisp",
    "books/arithmetic/natp-posp.lisp",
]


def parse_acl2_file(filepath: str) -> List[Dict[str, Any]]:
    """
    Parse an ACL2 .lisp file and extract defthm and defun forms.

    ACL2 proofs look like:
        (defthm theorem-name
          body
          :hints (("Goal" :in-theory (enable ...))))
    """
    results = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
    except OSError:
        return results

    # Extract defthm forms
    # Match balanced parens is hard; use a simpler heuristic
    pattern_thm = re.compile(
        r'\(defthm\s+(\S+)\s+(.*?)(?=\n\s*\(def|\n\s*\(in-theory|\n\s*\(include-book|\Z)',
        re.DOTALL
    )
    for m in pattern_thm.finditer(content):
        name = m.group(1).strip()
        body = m.group(2).strip()
        # Clean up body
        body_clean = re.sub(r'\s+', ' ', body)[:300]

        # Extract hints
        hints_match = re.search(r':hints\s*\((.*?)\)', body, re.DOTALL)
        hints = []
        if hints_match:
            hint_text = hints_match.group(1)
            hints = re.findall(r':(\w+)', hint_text)

        # Extract rule classes
        rules_match = re.search(r':rule-classes\s+(\S+)', body)
        rule_class = rules_match.group(1) if rules_match else "rewrite"

        results.append({
            "theorem": name,
            "goal": body_clean,
            "hints": hints,
            "rule_class": rule_class,
            "source": f"acl2/{os.path.basename(filepath)}",
        })

    return results


def download_acl2_files() -> int:
    """Attempt to download ACL2 community book files."""
    downloaded = 0
    for rel_path in ACL2_FILES:
        url = f"{ACL2_RAW_BASE}/{rel_path}"
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


def generate_synthetic_acl2() -> List[Dict[str, Any]]:
    """
    Generate high-quality synthetic ACL2 proofs.

    ACL2 proofs use a unique waterfall architecture: simplification,
    destructor elimination, cross-fertilization, generalization, and
    induction. Hints guide the prover.
    """
    arithmetic = [
        ("commutativity-of-+", "(equal (+ x y) (+ y x))", ":rule-classes :rewrite"),
        ("associativity-of-+", "(equal (+ (+ x y) z) (+ x (+ y z)))", ":rule-classes :rewrite"),
        ("commutativity-of-*", "(equal (* x y) (* y x))", ":rule-classes :rewrite"),
        ("associativity-of-*", "(equal (* (* x y) z) (* x (* y z)))", ":rule-classes :rewrite"),
        ("distributivity-of-*-over-+", "(equal (* x (+ y z)) (+ (* x y) (* x z)))", ":rule-classes :rewrite"),
        ("right-identity-of-+", "(equal (+ x 0) x)", ":rule-classes :rewrite"),
        ("left-identity-of-*", "(equal (* 1 x) x)", ":rule-classes :rewrite"),
        ("right-cancellation-for-+", "(implies (equal (+ a x) (+ b x)) (equal a b))", ':hints (("Goal" :use (:instance cancel-common)))'),
        ("natp-+", "(implies (and (natp x) (natp y)) (natp (+ x y)))", ':hints (("Goal" :in-theory (enable natp)))'),
        ("natp-*", "(implies (and (natp x) (natp y)) (natp (* x y)))", ':hints (("Goal" :in-theory (enable natp)))'),
        ("posp-implies-natp", "(implies (posp x) (natp x))", ':hints (("Goal" :in-theory (enable posp natp)))'),
        ("<=-reflexive", "(implies (natp x) (<= x x))", ":rule-classes :rewrite"),
        ("<=-transitive", "(implies (and (<= x y) (<= y z)) (<= x z))", ':hints (("Goal" :use (:instance transitivity-of-<=)))'),
        ("<=-antisymmetric", "(implies (and (<= x y) (<= y x)) (equal x y))", ':hints (("Goal" :use (:instance antisymmetry-of-<=)))'),
        ("floor-bounds", "(implies (and (natp x) (posp y)) (and (<= (* y (floor x y)) x) (< x (* y (+ 1 (floor x y))))))", ':hints (("Goal" :in-theory (enable floor)))'),
        ("mod-bounds", "(implies (and (natp x) (posp y)) (< (mod x y) y))", ':hints (("Goal" :in-theory (enable mod)))'),
        ("mod-+-cancel", "(implies (and (natp a) (natp b) (posp n)) (equal (mod (+ a (mod b n)) n) (mod (+ a b) n)))", ':hints (("Goal" :in-theory (enable mod)))'),
        ("expt-+", "(implies (and (natp m) (natp n)) (equal (expt b (+ m n)) (* (expt b m) (expt b n))))", ':hints (("Goal" :induct (expt b m)))'),
        ("evenp-+-2", "(implies (evenp x) (evenp (+ 2 x)))", ':hints (("Goal" :in-theory (enable evenp)))'),
        ("oddp-+-2", "(implies (oddp x) (oddp (+ 2 x)))", ':hints (("Goal" :in-theory (enable oddp)))'),
    ]

    lists = [
        ("true-listp-append", "(implies (true-listp x) (true-listp (append x y)))", ':hints (("Goal" :induct (true-listp x)))'),
        ("append-nil", "(implies (true-listp x) (equal (append x nil) x))", ':hints (("Goal" :induct (true-listp x)))'),
        ("associativity-of-append", "(equal (append (append x y) z) (append x (append y z)))", ':hints (("Goal" :induct (true-listp x)))'),
        ("len-append", "(equal (len (append x y)) (+ (len x) (len y)))", ':hints (("Goal" :induct (true-listp x)))'),
        ("len-revappend", "(equal (len (revappend x y)) (+ (len x) (len y)))", ':hints (("Goal" :induct (revappend x y)))'),
        ("revappend-revappend", "(equal (revappend (revappend x y) z) (revappend y (append x z)))", ':hints (("Goal" :induct (revappend x y)))'),
        ("reverse-reverse", "(implies (true-listp x) (equal (reverse (reverse x)) x))", ':hints (("Goal" :in-theory (enable reverse)))'),
        ("member-append", "(iff (member a (append x y)) (or (member a x) (member a y)))", ':hints (("Goal" :induct (true-listp x)))'),
        ("nth-of-append", "(implies (< (nfix n) (len x)) (equal (nth n (append x y)) (nth n x)))", ':hints (("Goal" :induct (nth n x)))'),
        ("car-cons", "(equal (car (cons x y)) x)", ":rule-classes :rewrite"),
        ("cdr-cons", "(equal (cdr (cons x y)) y)", ":rule-classes :rewrite"),
        ("cons-car-cdr", "(implies (consp x) (equal (cons (car x) (cdr x)) x))", ":rule-classes :rewrite"),
        ("len-nonnegative", "(<= 0 (len x))", ":rule-classes :type-prescription"),
        ("true-listp-revappend", "(implies (true-listp y) (true-listp (revappend x y)))", ':hints (("Goal" :induct (revappend x y)))'),
        ("nthcdr-of-append", "(implies (<= (nfix n) (len x)) (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))", ':hints (("Goal" :induct (nthcdr n x)))'),
    ]

    alists = [
        ("alistp-acons", "(implies (alistp a) (alistp (acons key val a)))", ':hints (("Goal" :in-theory (enable acons alistp)))'),
        ("assoc-of-acons", "(equal (assoc-equal key (acons key val a)) (cons key val))", ':hints (("Goal" :in-theory (enable acons assoc-equal)))'),
        ("assoc-of-acons-diff", "(implies (not (equal k1 k2)) (equal (assoc-equal k1 (acons k2 v a)) (assoc-equal k1 a)))", ':hints (("Goal" :in-theory (enable acons assoc-equal)))'),
        ("strip-cars-acons", "(equal (strip-cars (acons key val a)) (cons key (strip-cars a)))", ':hints (("Goal" :in-theory (enable acons strip-cars)))'),
        ("strip-cdrs-acons", "(equal (strip-cdrs (acons key val a)) (cons val (strip-cdrs a)))", ':hints (("Goal" :in-theory (enable acons strip-cdrs)))'),
    ]

    bitvectors = [
        ("logand-self", "(equal (logand x x) x)", ':hints (("Goal" :in-theory (enable logand)))'),
        ("logand-0", "(equal (logand x 0) 0)", ':hints (("Goal" :in-theory (enable logand)))'),
        ("logior-self", "(equal (logior x x) x)", ':hints (("Goal" :in-theory (enable logior)))'),
        ("logior-0", "(equal (logior x 0) x)", ':hints (("Goal" :in-theory (enable logior)))'),
        ("logxor-self", "(equal (logxor x x) 0)", ':hints (("Goal" :in-theory (enable logxor)))'),
        ("logxor-0", "(equal (logxor x 0) x)", ':hints (("Goal" :in-theory (enable logxor)))'),
        ("lognot-lognot", "(implies (integerp x) (equal (lognot (lognot x)) x))", ':hints (("Goal" :in-theory (enable lognot)))'),
        ("logand-comm", "(equal (logand x y) (logand y x))", ':hints (("Goal" :in-theory (enable logand)))'),
        ("logior-comm", "(equal (logior x y) (logior y x))", ':hints (("Goal" :in-theory (enable logior)))'),
        ("logxor-comm", "(equal (logxor x y) (logxor y x))", ':hints (("Goal" :in-theory (enable logxor)))'),
        ("ash-0", "(equal (ash x 0) (ifix x))", ':hints (("Goal" :in-theory (enable ash)))'),
        ("logbitp-of-logand", "(equal (logbitp n (logand x y)) (and (logbitp n x) (logbitp n y)))", ':hints (("Goal" :in-theory (enable logbitp logand)))'),
        ("unsigned-byte-p-of-logand", "(implies (or (unsigned-byte-p n x) (unsigned-byte-p n y)) (unsigned-byte-p n (logand x y)))", ':hints (("Goal" :in-theory (enable unsigned-byte-p logand)))'),
    ]

    sorting_search = [
        ("orderedp-merge", "(implies (and (orderedp x) (orderedp y)) (orderedp (merge-lists x y)))", ':hints (("Goal" :induct (merge-lists x y)))'),
        ("perm-merge", "(perm (append x y) (merge-lists x y))", ':hints (("Goal" :induct (merge-lists x y)))'),
        ("orderedp-msort", "(orderedp (msort x))", ':hints (("Goal" :induct (msort x)))'),
        ("perm-msort", "(perm x (msort x))", ':hints (("Goal" :induct (msort x)))'),
        ("orderedp-isort", "(orderedp (isort x))", ':hints (("Goal" :induct (isort x)))'),
        ("perm-isort", "(perm x (isort x))", ':hints (("Goal" :induct (isort x)))'),
        ("member-of-sorted", "(implies (and (orderedp x) (member a x) (member b x) (<= a b)) (member b (cdr (member a x))))", ':hints (("Goal" :induct (member a x)))'),
        ("bsearch-correct", "(implies (and (orderedp arr) (member key arr)) (equal (nth (bsearch key arr) arr) key))", ':hints (("Goal" :in-theory (enable bsearch)))'),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("lists", lists),
        ("alists", alists),
        ("bitvectors", bitvectors),
        ("sorting_search", sorting_search),
    ]

    proofs = []
    for category, theorems in all_categories:
        for name, goal, hints in theorems:
            hint_keywords = re.findall(r':(\w+)', hints)
            proofs.append({
                "theorem": name,
                "goal": f"(defthm {name} {goal})",
                "tactic_proof": f"(defthm {name} {goal} {hints})",
                "tactics": list(dict.fromkeys(hint_keywords))[:20],
                "source": f"acl2_synthetic/{category}",
            })
    return proofs


def run() -> Tuple[int, int]:
    """Run the full extraction pipeline."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(EXTERNAL_DIR, exist_ok=True)

    all_entries: List[Dict[str, Any]] = []
    extracted_count = 0

    print("[ACL2] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_acl2_files()
    print(f"  Downloaded/cached {downloaded} files")

    for fname in os.listdir(EXTERNAL_DIR):
        if fname.endswith(".lisp"):
            fpath = os.path.join(EXTERNAL_DIR, fname)
            parsed = parse_acl2_file(fpath)
            for entry in parsed:
                all_entries.append(entry)
            if parsed:
                print(f"  Parsed {len(parsed)} theorems from {fname}")
    extracted_count = len(all_entries)

    print(f"[ACL2] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_acl2()
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
            "prover": "ACL2",
            "theorem": entry["theorem"],
            "goal": entry["goal"],
            "context": entry.get("tactics", entry.get("hints", [])),
            "tactic_proof": entry.get("tactic_proof", ""),
            "source": entry.get("source", "acl2"),
        }
        output_records.append(record)
        current_id += 1

    with open(OUTPUT_FILE, "w", encoding="utf-8") as fh:
        for rec in output_records:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    stats = {
        "prover": "ACL2",
        "total_proofs": len(output_records),
        "extracted_from_source": extracted_count,
        "synthetic_added": len(output_records) - extracted_count,
        "id_range": [START_ID, current_id - 1],
        "output_file": OUTPUT_FILE,
    }
    with open(STATS_FILE, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2)

    print(f"\n[ACL2] COMPLETE: {len(output_records)} proofs written to {OUTPUT_FILE}")
    print(f"  Extracted from source: {extracted_count}")
    print(f"  Synthetic: {len(output_records) - extracted_count}")
    return extracted_count, len(output_records) - extracted_count


if __name__ == "__main__":
    run()
