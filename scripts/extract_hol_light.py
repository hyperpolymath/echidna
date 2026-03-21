#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from HOL Light corpus and convert to ECHIDNA training format.

Attempts to download from the HOL Light GitHub repository (Examples/ and
Multivariate/ directories). Falls back to generating high-quality synthetic
proofs from known HOL Light theorems if the download is unavailable.

HOL Light is a proof assistant for higher-order logic, known for its small
trusted kernel and the Flyspeck project (formal proof of the Kepler conjecture).

Output: training_data/proof_states_hol_light.jsonl
ID range: 90000+
"""

import json
import os
import re
import urllib.request
import urllib.error
from pathlib import Path
from typing import Dict, List, Any, Tuple

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTERNAL_DIR = os.path.join(REPO_ROOT, "external_corpora", "hol_light")
OUTPUT_DIR = os.path.join(REPO_ROOT, "training_data")
OUTPUT_FILE = os.path.join(OUTPUT_DIR, "proof_states_hol_light.jsonl")
STATS_FILE = os.path.join(OUTPUT_DIR, "stats_hol_light.json")
START_ID = 90000

# HOL Light source repository
HOL_LIGHT_RAW_BASE = (
    "https://raw.githubusercontent.com/jrh13/hol-light/master"
)

# Key files to attempt downloading
HOL_LIGHT_FILES = [
    "Examples/binary.ml",
    "Examples/combin.ml",
    "Examples/dickson.ml",
    "Examples/floor.ml",
    "Examples/hol88.ml",
    "Examples/forster.ml",
    "Examples/lagrange.ml",
    "Examples/miller_rabin.ml",
    "Examples/pell.ml",
    "Examples/prime.ml",
    "Examples/solovay.ml",
    "Examples/sylvester_gallai.ml",
    "Examples/wo.ml",
    "Multivariate/vectors.ml",
    "Multivariate/determinants.ml",
    "Multivariate/topology.ml",
    "Multivariate/convex.ml",
    "Multivariate/polytope.ml",
    "Multivariate/dimension.ml",
    "Multivariate/derivatives.ml",
    "Multivariate/integration.ml",
    "Multivariate/measure.ml",
]


# ---------------------------------------------------------------------------
# HOL Light proof parser
# ---------------------------------------------------------------------------

def parse_hol_light_file(filepath: str) -> List[Dict[str, Any]]:
    """
    Parse a HOL Light .ml file and extract theorem definitions.

    HOL Light theorems typically look like:
        let THEOREM_NAME = prove(
          `goal_term`,
          TACTIC_SEQUENCE);;

    We also capture 'let ... = prove ...' and 'let ... = PROVE ...' variants.
    """
    results = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
    except OSError:
        return results

    # Pattern: let THEOREM_NAME = prove(`goal`, tactic);;
    # HOL Light uses backtick-delimited terms
    pattern = re.compile(
        r'let\s+(\w+)\s*=\s*prove\s*\(\s*`([^`]+)`\s*,\s*(.*?)\)\s*;;',
        re.DOTALL
    )

    for match in pattern.finditer(content):
        theorem_name = match.group(1).strip()
        goal_text = match.group(2).strip().replace("\n", " ")
        tactic_text = match.group(3).strip().replace("\n", " ")
        # Compress whitespace
        goal_text = re.sub(r'\s+', ' ', goal_text)
        tactic_text = re.sub(r'\s+', ' ', tactic_text)

        # Extract tactic names (capitalized identifiers before arguments)
        tactic_names = re.findall(r'\b([A-Z][A-Z_]+(?:_TAC)?)\b', tactic_text)
        # Deduplicate while preserving order
        seen = set()
        tactics_unique = []
        for t in tactic_names:
            if t not in seen:
                seen.add(t)
                tactics_unique.append(t)

        source_file = os.path.basename(filepath)
        results.append({
            "theorem": theorem_name,
            "goal": goal_text,
            "tactic_proof": tactic_text[:500],  # Truncate very long proofs
            "tactics": tactics_unique[:20],
            "source": f"hol_light/{source_file}",
        })

    return results


def download_hol_light_files() -> int:
    """
    Attempt to download HOL Light example files from GitHub.

    Returns the number of files successfully downloaded.
    """
    downloaded = 0
    for rel_path in HOL_LIGHT_FILES:
        url = f"{HOL_LIGHT_RAW_BASE}/{rel_path}"
        local_path = os.path.join(EXTERNAL_DIR, rel_path.replace("/", "_"))
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


# ---------------------------------------------------------------------------
# Synthetic HOL Light proof generation
# ---------------------------------------------------------------------------

def generate_synthetic_hol_light() -> List[Dict[str, Any]]:
    """
    Generate high-quality synthetic HOL Light proofs based on well-known
    theorems and standard HOL Light tactic idioms.

    Each entry uses realistic HOL Light syntax and tactic sequences.
    """
    # Categories of theorems with realistic HOL Light formulations
    arithmetic_theorems = [
        ("ADD_SYM", "!m n. m + n = n + m", "INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]"),
        ("ADD_ASSOC", "!m n p. m + (n + p) = (m + n) + p", "INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]"),
        ("ADD_0", "!n. 0 + n = n", "INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]"),
        ("MULT_SYM", "!m n. m * n = n * m", "INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ARITH_TAC"),
        ("MULT_ASSOC", "!m n p. m * (n * p) = (m * n) * p", "INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LEFT_ADD_DISTRIB]"),
        ("MULT_0", "!n. 0 * n = 0", "REWRITE_TAC[MULT_CLAUSES]"),
        ("LEFT_ADD_DISTRIB", "!m n p. m * (n + p) = m * n + m * p", "INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ADD_ASSOC]"),
        ("EXP_ADD", "!m n p. m EXP (n + p) = m EXP n * m EXP p", "INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; ADD_CLAUSES; MULT_CLAUSES; MULT_ASSOC]"),
        ("ADD_SUC", "!m n. m + SUC n = SUC (m + n)", "REWRITE_TAC[ADD_CLAUSES]"),
        ("MULT_SUC", "!m n. m * SUC n = m + m * n", "REWRITE_TAC[MULT_CLAUSES]"),
        ("LE_REFL", "!n. n <= n", "REWRITE_TAC[LE_REFL]"),
        ("LE_TRANS", "!m n p. m <= n /\\ n <= p ==> m <= p", "ARITH_TAC"),
        ("LE_ANTISYM", "!m n. m <= n /\\ n <= m ==> m = n", "ARITH_TAC"),
        ("LT_ADD", "!m n. 0 < n ==> m < m + n", "ARITH_TAC"),
        ("EVEN_ADD", "!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)", "INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; EVEN]"),
        ("ODD_ADD", "!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)", "REWRITE_TAC[GSYM NOT_EVEN; EVEN_ADD] THEN MESON_TAC[]"),
        ("DIVMOD_EXIST", "!m n. ~(n = 0) ==> ?q r. m = q * n + r /\\ r < n", "MESON_TAC[DIVISION]"),
        ("FACT_LT", "!n. 0 < FACT n", "INDUCT_TAC THEN ASM_REWRITE_TAC[FACT; LT_MULT] THEN ARITH_TAC"),
        ("FIB_ADD", "!m n. fib(m + n + 1) = fib(m + 1) * fib(n + 1) + fib(m) * fib(n)", "INDUCT_TAC THEN ASM_REWRITE_TAC[FIB; ADD_CLAUSES; MULT_CLAUSES]"),
        ("PRIME_2", "prime 2", "REWRITE_TAC[prime] THEN ARITH_TAC"),
    ]

    logic_theorems = [
        ("AND_SYM", "!p q. p /\\ q <=> q /\\ p", "MESON_TAC[]"),
        ("OR_SYM", "!p q. p \\/ q <=> q \\/ p", "MESON_TAC[]"),
        ("IMP_TRANS", "!p q r. (p ==> q) /\\ (q ==> r) ==> (p ==> r)", "MESON_TAC[]"),
        ("CONTRAPOSITIVE", "!p q. (p ==> q) <=> (~q ==> ~p)", "MESON_TAC[]"),
        ("DE_MORGAN_AND", "!p q. ~(p /\\ q) <=> ~p \\/ ~q", "MESON_TAC[]"),
        ("DE_MORGAN_OR", "!p q. ~(p \\/ q) <=> ~p /\\ ~q", "MESON_TAC[]"),
        ("DOUBLE_NEG", "!p. ~~p <=> p", "MESON_TAC[]"),
        ("EXCLUDED_MIDDLE", "!p. p \\/ ~p", "MESON_TAC[]"),
        ("AND_ASSOC", "!p q r. p /\\ (q /\\ r) <=> (p /\\ q) /\\ r", "MESON_TAC[]"),
        ("OR_ASSOC", "!p q r. p \\/ (q \\/ r) <=> (p \\/ q) \\/ r", "MESON_TAC[]"),
        ("IMP_IMP", "!p q r. (p ==> q ==> r) <=> (p /\\ q ==> r)", "MESON_TAC[]"),
        ("FORALL_AND", "!P Q. (!x. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)", "MESON_TAC[]"),
        ("EXISTS_OR", "!P Q. (?x. P x \\/ Q x) <=> (?x. P x) \\/ (?x. Q x)", "MESON_TAC[]"),
        ("NOT_FORALL", "!P. ~(!x. P x) <=> (?x. ~P x)", "MESON_TAC[]"),
        ("NOT_EXISTS", "!P. ~(?x. P x) <=> (!x. ~P x)", "MESON_TAC[]"),
    ]

    set_theorems = [
        ("SUBSET_REFL", "!s:A->bool. s SUBSET s", "SET_TAC[]"),
        ("SUBSET_TRANS", "!s t u:A->bool. s SUBSET t /\\ t SUBSET u ==> s SUBSET u", "SET_TAC[]"),
        ("INTER_COMM", "!s t:A->bool. s INTER t = t INTER s", "SET_TAC[]"),
        ("UNION_COMM", "!s t:A->bool. s UNION t = t UNION s", "SET_TAC[]"),
        ("INTER_ASSOC", "!s t u:A->bool. s INTER (t INTER u) = (s INTER t) INTER u", "SET_TAC[]"),
        ("UNION_ASSOC", "!s t u:A->bool. s UNION (t UNION u) = (s UNION t) UNION u", "SET_TAC[]"),
        ("INTER_SUBSET", "!s t:A->bool. (s INTER t) SUBSET s", "SET_TAC[]"),
        ("SUBSET_UNION", "!s t:A->bool. s SUBSET (s UNION t)", "SET_TAC[]"),
        ("EMPTY_SUBSET", "!s:A->bool. EMPTY SUBSET s", "SET_TAC[]"),
        ("SUBSET_EMPTY", "!s:A->bool. s SUBSET EMPTY <=> s = EMPTY", "SET_TAC[]"),
        ("UNION_EMPTY", "!s:A->bool. s UNION EMPTY = s", "SET_TAC[]"),
        ("INTER_UNIV", "!s:A->bool. s INTER UNIV = s", "SET_TAC[]"),
        ("DE_MORGAN_INTER", "!s t:A->bool. UNIV DIFF (s INTER t) = (UNIV DIFF s) UNION (UNIV DIFF t)", "SET_TAC[]"),
        ("ABSORPTION_UNION", "!s t:A->bool. s SUBSET t ==> s UNION t = t", "SET_TAC[]"),
        ("DISJOINT_SYM", "!s t:A->bool. DISJOINT s t <=> DISJOINT t s", "SET_TAC[DISJOINT]"),
    ]

    list_theorems = [
        ("APPEND_NIL", "!l:(A)list. APPEND l [] = l", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]"),
        ("APPEND_ASSOC", "!l1 l2 l3:(A)list. APPEND l1 (APPEND l2 l3) = APPEND (APPEND l1 l2) l3", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]"),
        ("LENGTH_APPEND", "!l1 l2:(A)list. LENGTH(APPEND l1 l2) = LENGTH l1 + LENGTH l2", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES]"),
        ("REVERSE_REVERSE", "!l:(A)list. REVERSE(REVERSE l) = l", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; REVERSE_APPEND]"),
        ("MAP_APPEND", "!f l1 l2:(A)list. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]"),
        ("LENGTH_MAP", "!f l:(A)list. LENGTH(MAP f l) = LENGTH l", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH]"),
        ("MAP_ID", "!l:(A)list. MAP (\\x. x) l = l", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]"),
        ("FILTER_APPEND", "!P l1 l2:(A)list. FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]"),
        ("MEM_APPEND", "!x l1 l2:(A)list. MEM x (APPEND l1 l2) <=> MEM x l1 \\/ MEM x l2", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; APPEND] THEN MESON_TAC[]"),
        ("ALL_APPEND", "!P l1 l2:(A)list. ALL P (APPEND l1 l2) <=> ALL P l1 /\\ ALL P l2", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; APPEND] THEN MESON_TAC[]"),
    ]

    real_analysis = [
        ("REAL_ADD_SYM", "!x y. x + y = y + x", "REAL_ARITH_TAC"),
        ("REAL_ADD_ASSOC", "!x y z. x + (y + z) = (x + y) + z", "REAL_ARITH_TAC"),
        ("REAL_MUL_SYM", "!x y. x * y = y * x", "REAL_ARITH_TAC"),
        ("REAL_LE_TOTAL", "!x y. x <= y \\/ y <= x", "REAL_ARITH_TAC"),
        ("ABS_TRIANGLE", "!x y. abs(x + y) <= abs(x) + abs(y)", "REAL_ARITH_TAC"),
        ("ABS_POS", "!x. &0 <= abs(x)", "REAL_ARITH_TAC"),
        ("ABS_ZERO", "!x. abs(x) = &0 <=> x = &0", "REAL_ARITH_TAC"),
        ("REAL_POW_ADD", "!x m n. x pow (m + n) = x pow m * x pow n", "INDUCT_TAC THEN ASM_REWRITE_TAC[real_pow; ADD_CLAUSES; REAL_MUL_LID; REAL_MUL_ASSOC]"),
        ("SQRT_POW_2", "!x. &0 <= x ==> sqrt(x) pow 2 = x", "MESON_TAC[SQRT_POW2]"),
        ("REAL_COMPLETE", "!P. (?x. P x) /\\ (?M. !x. P x ==> x <= M) ==> ?s. (!x. P x ==> x <= s) /\\ !M. (!x. P x ==> x <= M) ==> s <= M", "REWRITE_TAC[REAL_COMPLETE]"),
        ("LIM_CONST", "!net c. (\\x. c) --> c", "REWRITE_TAC[LIM; dist; REAL_SUB_REFL; ABS_0]"),
        ("LIM_ADD", "!net f g l m. f --> l /\\ g --> m ==> (\\x. f x + g x) --> l + m", "REWRITE_TAC[LIM] THEN MESON_TAC[ABS_TRIANGLE; REAL_ARITH]"),
        ("CONTINUOUS_ADD", "!f g x. f continuous_at x /\\ g continuous_at x ==> (\\y. f y + g y) continuous_at x", "REWRITE_TAC[continuous_at] THEN MESON_TAC[LIM_ADD]"),
        ("IVT", "!f a b. f continuous_on real_interval[a,b] /\\ f(a) <= &0 /\\ &0 <= f(b) ==> ?c. a <= c /\\ c <= b /\\ f(c) = &0", "MATCH_MP_TAC IVT_INCREASING THEN ASM_REWRITE_TAC[]"),
        ("MVT", "!f f' a b. (!x. a <= x /\\ x <= b ==> (f has_real_derivative f' x) (atreal x within real_interval[a,b])) /\\ a < b ==> ?c. a < c /\\ c < b /\\ f(b) - f(a) = f'(c) * (b - a)", "MATCH_MP_TAC REAL_MVT_VERY_SIMPLE THEN ASM_REWRITE_TAC[]"),
    ]

    topology_theorems = [
        ("OPEN_EMPTY", "open({}:real^N->bool)", "REWRITE_TAC[OPEN_EMPTY]"),
        ("OPEN_UNIV", "open((:real^N))", "REWRITE_TAC[OPEN_UNIV]"),
        ("OPEN_INTER", "!s t:real^N->bool. open s /\\ open t ==> open(s INTER t)", "MESON_TAC[OPEN_INTER]"),
        ("OPEN_UNION", "!s t:real^N->bool. open s /\\ open t ==> open(s UNION t)", "MESON_TAC[OPEN_UNION]"),
        ("CLOSED_EMPTY", "closed({}:real^N->bool)", "REWRITE_TAC[CLOSED_EMPTY]"),
        ("CLOSED_UNIV", "closed((:real^N))", "REWRITE_TAC[CLOSED_UNIV]"),
        ("CLOSED_INTER", "!s t:real^N->bool. closed s /\\ closed t ==> closed(s INTER t)", "MESON_TAC[CLOSED_INTER]"),
        ("COMPACT_IMP_CLOSED", "!s:real^N->bool. compact s ==> closed s", "MESON_TAC[COMPACT_IMP_CLOSED]"),
        ("COMPACT_IMP_BOUNDED", "!s:real^N->bool. compact s ==> bounded s", "MESON_TAC[COMPACT_IMP_BOUNDED]"),
        ("HEINE_BOREL", "!s:real^N->bool. compact s <=> closed s /\\ bounded s", "REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED]"),
        ("CONNECTED_INTERVAL", "!a b:real^N. connected(interval[a,b])", "REWRITE_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL]"),
        ("BROUWER_FIXED_POINT", "!f s:real^N->bool. compact s /\\ convex s /\\ ~(s = {}) /\\ f continuous_on s /\\ IMAGE f s SUBSET s ==> ?x. x IN s /\\ f x = x", "MATCH_MP_TAC BROUWER_FIXED_POINT THEN ASM_REWRITE_TAC[]"),
    ]

    # Combine all theorem categories
    all_categories = [
        ("arithmetic", arithmetic_theorems),
        ("logic", logic_theorems),
        ("sets", set_theorems),
        ("lists", list_theorems),
        ("real_analysis", real_analysis),
        ("topology", topology_theorems),
    ]

    proofs = []
    for category, theorems in all_categories:
        for name, goal, tactic in theorems:
            # Extract tactic names from the tactic string
            tactic_names = re.findall(r'\b([A-Z][A-Z_]+(?:_TAC)?)\b', tactic)
            seen = set()
            tactics_unique = []
            for t in tactic_names:
                if t not in seen:
                    seen.add(t)
                    tactics_unique.append(t)

            proofs.append({
                "theorem": name,
                "goal": goal,
                "tactic_proof": tactic,
                "tactics": tactics_unique,
                "source": f"hol_light_synthetic/{category}",
            })

    return proofs


# ---------------------------------------------------------------------------
# Main extraction pipeline
# ---------------------------------------------------------------------------

def run() -> Tuple[int, int]:
    """
    Run the full extraction pipeline.

    Returns (extracted_count, synthetic_count).
    """
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(EXTERNAL_DIR, exist_ok=True)

    all_entries: List[Dict[str, Any]] = []
    extracted_count = 0

    # Phase 1: try downloading real HOL Light files
    print("[HOL Light] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_hol_light_files()
    print(f"  Downloaded/cached {downloaded} files")

    # Parse whatever we got
    for fname in os.listdir(EXTERNAL_DIR):
        if fname.endswith(".ml"):
            fpath = os.path.join(EXTERNAL_DIR, fname)
            parsed = parse_hol_light_file(fpath)
            for entry in parsed:
                all_entries.append(entry)
            if parsed:
                print(f"  Parsed {len(parsed)} theorems from {fname}")
    extracted_count = len(all_entries)

    # Phase 2: always add synthetic data (supplements real data)
    print(f"[HOL Light] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_hol_light()
    # Avoid duplicates by theorem name
    existing_names = {e["theorem"] for e in all_entries}
    added = 0
    for entry in synthetic:
        if entry["theorem"] not in existing_names:
            all_entries.append(entry)
            existing_names.add(entry["theorem"])
            added += 1
    print(f"  Generated {added} unique synthetic proofs")

    # Assign IDs and normalise schema
    current_id = START_ID
    output_records = []
    for entry in all_entries:
        record = {
            "id": current_id,
            "prover": "HOLLight",
            "theorem": entry["theorem"],
            "goal": entry["goal"],
            "context": entry.get("tactics", []),
            "tactic_proof": entry.get("tactic_proof", ""),
            "source": entry.get("source", "hol_light"),
        }
        output_records.append(record)
        current_id += 1

    # Write output
    with open(OUTPUT_FILE, "w", encoding="utf-8") as fh:
        for rec in output_records:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    # Write stats
    stats = {
        "prover": "HOLLight",
        "total_proofs": len(output_records),
        "extracted_from_source": extracted_count,
        "synthetic_added": len(output_records) - extracted_count,
        "id_range": [START_ID, current_id - 1],
        "output_file": OUTPUT_FILE,
    }
    with open(STATS_FILE, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2)

    print(f"\n[HOL Light] COMPLETE: {len(output_records)} proofs written to {OUTPUT_FILE}")
    print(f"  Extracted from source: {extracted_count}")
    print(f"  Synthetic: {len(output_records) - extracted_count}")
    return extracted_count, len(output_records) - extracted_count


if __name__ == "__main__":
    run()
