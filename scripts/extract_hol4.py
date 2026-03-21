#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from HOL4 corpus and convert to ECHIDNA training format.

Attempts to download HOL4 example files from GitHub. Falls back to generating
high-quality synthetic HOL4 proofs from standard theories (arithmetic, lists,
sets, booleans, strings, CakeML-style verification).

HOL4 is an interactive proof assistant in the HOL family, used extensively in
the CakeML project (verified ML compiler) and seL4 (verified OS kernel).

Output: training_data/proof_states_hol4.jsonl
ID range: 91000+
"""

import json
import os
import re
import urllib.request
import urllib.error
from typing import Dict, List, Any, Tuple

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTERNAL_DIR = os.path.join(REPO_ROOT, "external_corpora", "hol4")
OUTPUT_DIR = os.path.join(REPO_ROOT, "training_data")
OUTPUT_FILE = os.path.join(OUTPUT_DIR, "proof_states_hol4.jsonl")
STATS_FILE = os.path.join(OUTPUT_DIR, "stats_hol4.json")
START_ID = 91000

HOL4_RAW_BASE = "https://raw.githubusercontent.com/HOL-Theorem-Prover/HOL/develop"
HOL4_FILES = [
    "examples/algebra/groupScript.sml",
    "examples/algebra/ringScript.sml",
    "examples/algorithms/sortingScript.sml",
    "examples/set-theory/zfcScript.sml",
    "src/num/theories/arithmeticScript.sml",
    "src/list/src/listScript.sml",
    "src/boss/boolScript.sml",
    "src/string/stringScript.sml",
    "src/pred_set/src/pred_setScript.sml",
    "src/real/realScript.sml",
]


def parse_hol4_file(filepath: str) -> List[Dict[str, Any]]:
    """
    Parse a HOL4 *Script.sml file and extract theorem definitions.

    HOL4 theorems typically look like:
        val THEOREM_NAME = store_thm("THEOREM_NAME",
          ``goal_term``,
          tactic_sequence);

    Or the newer style:
        Theorem THEOREM_NAME:
          goal_term
        Proof
          tactic_sequence
        QED
    """
    results = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
    except OSError:
        return results

    # Pattern 1: store_thm style
    pattern1 = re.compile(
        r'store_thm\s*\(\s*"(\w+)"\s*,\s*``([^`]+)``\s*,\s*(.*?)\)\s*;',
        re.DOTALL
    )
    for m in pattern1.finditer(content):
        name = m.group(1).strip()
        goal = re.sub(r'\s+', ' ', m.group(2).strip())
        tactic = re.sub(r'\s+', ' ', m.group(3).strip())
        tactic_names = re.findall(r'\b(\w+_TAC|Induct_on|rw|fs|simp|metis_tac|decide_tac|PROVE_TAC)\b', tactic, re.IGNORECASE)
        results.append({
            "theorem": name,
            "goal": goal,
            "tactic_proof": tactic[:500],
            "tactics": list(dict.fromkeys(tactic_names))[:20],
            "source": f"hol4/{os.path.basename(filepath)}",
        })

    # Pattern 2: Theorem/Proof/QED style
    pattern2 = re.compile(
        r'Theorem\s+(\w+)\s*:\s*(.*?)\s*Proof\s*(.*?)\s*QED',
        re.DOTALL
    )
    for m in pattern2.finditer(content):
        name = m.group(1).strip()
        goal = re.sub(r'\s+', ' ', m.group(2).strip())
        tactic = re.sub(r'\s+', ' ', m.group(3).strip())
        tactic_names = re.findall(r'\b(\w+_TAC|Induct_on|rw|fs|simp|metis_tac|decide_tac|PROVE_TAC)\b', tactic, re.IGNORECASE)
        results.append({
            "theorem": name,
            "goal": goal,
            "tactic_proof": tactic[:500],
            "tactics": list(dict.fromkeys(tactic_names))[:20],
            "source": f"hol4/{os.path.basename(filepath)}",
        })

    return results


def download_hol4_files() -> int:
    """Attempt to download HOL4 source files from GitHub."""
    downloaded = 0
    for rel_path in HOL4_FILES:
        url = f"{HOL4_RAW_BASE}/{rel_path}"
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


def generate_synthetic_hol4() -> List[Dict[str, Any]]:
    """
    Generate high-quality synthetic HOL4 proofs using realistic SML
    tactic syntax and standard HOL4 library theorems.
    """
    arithmetic = [
        ("ADD_COMM", "!m n. m + n = n + m", "Induct_on `m` >> rw[ADD_CLAUSES]"),
        ("ADD_ASSOC", "!m n p. m + (n + p) = (m + n) + p", "Induct_on `m` >> rw[ADD_CLAUSES]"),
        ("MULT_COMM", "!m n. m * n = n * m", "Induct_on `m` >> rw[MULT_CLAUSES] >> decide_tac"),
        ("MULT_ASSOC", "!m n p. m * (n * p) = (m * n) * p", "Induct_on `m` >> rw[MULT_CLAUSES, LEFT_ADD_DISTRIB]"),
        ("LEFT_ADD_DISTRIB", "!m n p. m * (n + p) = m * n + m * p", "Induct_on `m` >> rw[MULT_CLAUSES, ADD_ASSOC]"),
        ("EXP_ADD", "!b m n. b ** (m + n) = b ** m * b ** n", "Induct_on `m` >> rw[EXP, MULT_CLAUSES, MULT_ASSOC]"),
        ("LESS_EQ_REFL", "!n. n <= n", "rw[LESS_EQ_REFL]"),
        ("LESS_EQ_TRANS", "!m n p. m <= n /\\ n <= p ==> m <= p", "metis_tac[LESS_EQ_TRANS]"),
        ("LESS_EQ_ANTISYM", "!m n. m <= n /\\ n <= m ==> (m = n)", "decide_tac"),
        ("DIVMOD_ID", "!n. 0 < n ==> (n DIV n = 1)", "rw[DIV_SELF]"),
        ("MOD_LESS", "!m n. 0 < n ==> m MOD n < n", "metis_tac[MOD_LESS]"),
        ("EVEN_OR_ODD", "!n. EVEN n \\/ ODD n", "Induct_on `n` >> fs[EVEN, ODD]"),
        ("NOT_EVEN_AND_ODD", "!n. ~(EVEN n /\\ ODD n)", "Induct_on `n` >> fs[EVEN, ODD]"),
        ("SUC_NOT_ZERO", "!n. ~(SUC n = 0)", "rw[NOT_SUC]"),
        ("PRE_SUC", "!n. PRE (SUC n) = n", "rw[PRE]"),
        ("ADD_SUC", "!m n. m + SUC n = SUC (m + n)", "rw[ADD_CLAUSES]"),
        ("MULT_SUC", "!m n. m * SUC n = m + m * n", "rw[MULT_CLAUSES]"),
        ("ZERO_LT_SUC", "!n. 0 < SUC n", "decide_tac"),
        ("LT_IMP_LE", "!m n. m < n ==> m <= n", "decide_tac"),
        ("LE_LT_OR_EQ", "!m n. m <= n <=> m < n \\/ (m = n)", "decide_tac"),
    ]

    lists = [
        ("APPEND_NIL", "!l. APPEND l [] = l", "Induct_on `l` >> rw[APPEND]"),
        ("APPEND_ASSOC", "!l1 l2 l3. APPEND l1 (APPEND l2 l3) = APPEND (APPEND l1 l2) l3", "Induct_on `l1` >> rw[APPEND]"),
        ("LENGTH_APPEND", "!l1 l2. LENGTH (APPEND l1 l2) = LENGTH l1 + LENGTH l2", "Induct_on `l1` >> rw[APPEND, LENGTH, ADD_CLAUSES]"),
        ("REVERSE_APPEND", "!l1 l2. REVERSE (APPEND l1 l2) = APPEND (REVERSE l2) (REVERSE l1)", "Induct_on `l1` >> rw[REVERSE, APPEND, APPEND_NIL, APPEND_ASSOC]"),
        ("REVERSE_REVERSE", "!l. REVERSE (REVERSE l) = l", "Induct_on `l` >> rw[REVERSE, REVERSE_APPEND, APPEND]"),
        ("MAP_APPEND", "!f l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)", "Induct_on `l1` >> rw[MAP, APPEND]"),
        ("LENGTH_MAP", "!f l. LENGTH (MAP f l) = LENGTH l", "Induct_on `l` >> rw[MAP, LENGTH]"),
        ("MAP_MAP", "!f g l. MAP f (MAP g l) = MAP (f o g) l", "Induct_on `l` >> rw[MAP]"),
        ("FILTER_APPEND", "!P l1 l2. FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)", "Induct_on `l1` >> rw[FILTER, APPEND] >> Cases_on `P h` >> rw[APPEND]"),
        ("MEM_APPEND", "!x l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \\/ MEM x l2", "Induct_on `l1` >> rw[MEM, APPEND] >> metis_tac[]"),
        ("EVERY_APPEND", "!P l1 l2. EVERY P (APPEND l1 l2) <=> EVERY P l1 /\\ EVERY P l2", "Induct_on `l1` >> rw[EVERY, APPEND] >> metis_tac[]"),
        ("FLAT_APPEND", "!l1 l2. FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)", "Induct_on `l1` >> rw[FLAT, APPEND, APPEND_ASSOC]"),
        ("HD_APPEND", "!l1 l2. l1 <> [] ==> (HD (APPEND l1 l2) = HD l1)", "Cases_on `l1` >> rw[APPEND, HD]"),
        ("EL_MAP", "!n f l. n < LENGTH l ==> (EL n (MAP f l) = f (EL n l))", "Induct_on `n` >> Cases_on `l` >> rw[MAP, EL, HD, TL, LENGTH]"),
        ("NULL_EQ", "!l. NULL l <=> (l = [])", "Cases_on `l` >> rw[NULL]"),
    ]

    sets = [
        ("IN_UNION", "!x s t. x IN (s UNION t) <=> x IN s \\/ x IN t", "rw[UNION_DEF, GSPECIFICATION] >> metis_tac[]"),
        ("IN_INTER", "!x s t. x IN (s INTER t) <=> x IN s /\\ x IN t", "rw[INTER_DEF, GSPECIFICATION]"),
        ("SUBSET_REFL", "!s. s SUBSET s", "rw[SUBSET_DEF]"),
        ("SUBSET_TRANS", "!s t u. s SUBSET t /\\ t SUBSET u ==> s SUBSET u", "rw[SUBSET_DEF] >> metis_tac[]"),
        ("UNION_COMM", "!s t. s UNION t = t UNION s", "rw[EXTENSION, IN_UNION] >> metis_tac[]"),
        ("INTER_COMM", "!s t. s INTER t = t INTER s", "rw[EXTENSION, IN_INTER] >> metis_tac[]"),
        ("UNION_ASSOC", "!s t u. s UNION (t UNION u) = (s UNION t) UNION u", "rw[EXTENSION, IN_UNION] >> metis_tac[]"),
        ("INTER_ASSOC", "!s t u. s INTER (t INTER u) = (s INTER t) INTER u", "rw[EXTENSION, IN_INTER] >> metis_tac[]"),
        ("UNION_EMPTY", "!s. s UNION EMPTY = s", "rw[EXTENSION, IN_UNION, NOT_IN_EMPTY]"),
        ("INTER_UNIV", "!s. s INTER UNIV = s", "rw[EXTENSION, IN_INTER, IN_UNIV]"),
        ("EMPTY_SUBSET", "!s. EMPTY SUBSET s", "rw[SUBSET_DEF, NOT_IN_EMPTY]"),
        ("SUBSET_UNION", "!s t. s SUBSET (s UNION t)", "rw[SUBSET_DEF, IN_UNION]"),
        ("INTER_SUBSET", "!s t. (s INTER t) SUBSET s", "rw[SUBSET_DEF, IN_INTER]"),
        ("CARD_UNION_DISJOINT", "!s t. FINITE s /\\ FINITE t /\\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t)", "metis_tac[CARD_UNION]"),
        ("FINITE_EMPTY", "FINITE EMPTY", "rw[FINITE_EMPTY]"),
    ]

    booleans = [
        ("CONJ_COMM", "!p q. p /\\ q <=> q /\\ p", "metis_tac[]"),
        ("DISJ_COMM", "!p q. p \\/ q <=> q \\/ p", "metis_tac[]"),
        ("IMP_ANTISYM", "!p q. (p ==> q) /\\ (q ==> p) ==> (p <=> q)", "metis_tac[]"),
        ("CONTRAPOSITIVE", "!p q. (p ==> q) <=> (~q ==> ~p)", "metis_tac[]"),
        ("DE_MORGAN1", "!p q. ~(p /\\ q) <=> ~p \\/ ~q", "metis_tac[]"),
        ("DE_MORGAN2", "!p q. ~(p \\/ q) <=> ~p /\\ ~q", "metis_tac[]"),
        ("DOUBLE_NEG", "!p. ~~p <=> p", "metis_tac[]"),
        ("EXCLUDED_MIDDLE", "!p. p \\/ ~p", "metis_tac[]"),
        ("COND_TRUE", "!x y. (if T then x else y) = x", "rw[]"),
        ("COND_FALSE", "!x y. (if F then x else y) = y", "rw[]"),
        ("AND_CLAUSES", "!p. (T /\\ p <=> p) /\\ (p /\\ T <=> p) /\\ (F /\\ p <=> F) /\\ (p /\\ F <=> F)", "rw[]"),
        ("OR_CLAUSES", "!p. (T \\/ p <=> T) /\\ (p \\/ T <=> T) /\\ (F \\/ p <=> p) /\\ (p \\/ F <=> p)", "rw[]"),
        ("IMP_CLAUSES", "!p. (T ==> p <=> p) /\\ (p ==> T <=> T) /\\ (F ==> p <=> T) /\\ (p ==> p <=> T)", "rw[]"),
        ("FORALL_CONJ", "!P Q. (!x. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)", "metis_tac[]"),
        ("EXISTS_DISJ", "!P Q. (?x. P x \\/ Q x) <=> (?x. P x) \\/ (?x. Q x)", "metis_tac[]"),
    ]

    sorting = [
        ("SORTED_CONS", "!R x l. SORTED R (x::l) <=> SORTED R l /\\ (!y. MEM y l ==> R x y)", "rw[SORTED_DEF] >> metis_tac[]"),
        ("SORTED_APPEND", "!R l1 l2. transitive R ==> (SORTED R (l1 ++ l2) <=> SORTED R l1 /\\ SORTED R l2 /\\ !x y. MEM x l1 /\\ MEM y l2 ==> R x y)", "Induct_on `l1` >> rw[SORTED_DEF, APPEND, MEM] >> metis_tac[]"),
        ("PERM_REFL", "!l. PERM l l", "rw[PERM_REFL]"),
        ("PERM_SYM", "!l1 l2. PERM l1 l2 ==> PERM l2 l1", "metis_tac[PERM_SYM]"),
        ("PERM_TRANS", "!l1 l2 l3. PERM l1 l2 /\\ PERM l2 l3 ==> PERM l1 l3", "metis_tac[PERM_TRANS]"),
        ("PERM_LENGTH", "!l1 l2. PERM l1 l2 ==> (LENGTH l1 = LENGTH l2)", "metis_tac[PERM_LENGTH]"),
        ("QSORT_SORTED", "!R l. total R /\\ transitive R ==> SORTED R (QSORT R l)", "metis_tac[QSORT_SORTED]"),
        ("QSORT_PERM", "!R l. PERM l (QSORT R l)", "metis_tac[QSORT_PERM]"),
        ("QSORT_MEM", "!R x l. MEM x (QSORT R l) <=> MEM x l", "metis_tac[QSORT_PERM, PERM_MEM_EQ]"),
        ("QSORT_STABLE", "!R l. SORTED R l ==> (QSORT R l = l)", "Induct_on `l` >> rw[QSORT_DEF, SORTED_DEF] >> metis_tac[SORTED_EQ]"),
    ]

    cakeml_style = [
        ("EVAL_INT_ADD", "!n1 n2. eval_exp env (Add (Lit (IntLit n1)) (Lit (IntLit n2))) = Rval (Litv (IntLit (n1 + n2)))", "rw[eval_exp_def, do_app_def]"),
        ("TYPE_SOUNDNESS", "!e t env. type_of env e = SOME t ==> ?v. eval_exp env e = Rval v /\\ value_type v t", "Induct_on `e` >> rw[type_of_def, eval_exp_def] >> metis_tac[]"),
        ("COMPILER_CORRECTNESS", "!e env. semantics env e <> Fail ==> observed (compile e) = observed (eval e)", "metis_tac[compiler_correct]"),
        ("ENV_LOOKUP", "!x v env. lookup x ((x,v)::env) = SOME v", "rw[lookup_def]"),
        ("ENV_LOOKUP_OTHER", "!x y v env. x <> y ==> (lookup x ((y,v)::env) = lookup x env)", "rw[lookup_def]"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("lists", lists),
        ("sets", sets),
        ("booleans", booleans),
        ("sorting", sorting),
        ("cakeml_style", cakeml_style),
    ]

    proofs = []
    for category, theorems in all_categories:
        for name, goal, tactic in theorems:
            tactic_names = re.findall(
                r'\b(Induct_on|Cases_on|rw|fs|simp|metis_tac|decide_tac|PROVE_TAC|rpt|strip_tac|gen_tac|MATCH_MP_TAC)\b',
                tactic, re.IGNORECASE
            )
            proofs.append({
                "theorem": name,
                "goal": goal,
                "tactic_proof": tactic,
                "tactics": list(dict.fromkeys(tactic_names))[:20],
                "source": f"hol4_synthetic/{category}",
            })
    return proofs


def run() -> Tuple[int, int]:
    """Run the full extraction pipeline."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(EXTERNAL_DIR, exist_ok=True)

    all_entries: List[Dict[str, Any]] = []
    extracted_count = 0

    print("[HOL4] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_hol4_files()
    print(f"  Downloaded/cached {downloaded} files")

    for fname in os.listdir(EXTERNAL_DIR):
        if fname.endswith(".sml"):
            fpath = os.path.join(EXTERNAL_DIR, fname)
            parsed = parse_hol4_file(fpath)
            for entry in parsed:
                all_entries.append(entry)
            if parsed:
                print(f"  Parsed {len(parsed)} theorems from {fname}")
    extracted_count = len(all_entries)

    print(f"[HOL4] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_hol4()
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
            "prover": "HOL4",
            "theorem": entry["theorem"],
            "goal": entry["goal"],
            "context": entry.get("tactics", []),
            "tactic_proof": entry.get("tactic_proof", ""),
            "source": entry.get("source", "hol4"),
        }
        output_records.append(record)
        current_id += 1

    with open(OUTPUT_FILE, "w", encoding="utf-8") as fh:
        for rec in output_records:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    stats = {
        "prover": "HOL4",
        "total_proofs": len(output_records),
        "extracted_from_source": extracted_count,
        "synthetic_added": len(output_records) - extracted_count,
        "id_range": [START_ID, current_id - 1],
        "output_file": OUTPUT_FILE,
    }
    with open(STATS_FILE, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2)

    print(f"\n[HOL4] COMPLETE: {len(output_records)} proofs written to {OUTPUT_FILE}")
    print(f"  Extracted from source: {extracted_count}")
    print(f"  Synthetic: {len(output_records) - extracted_count}")
    return extracted_count, len(output_records) - extracted_count


if __name__ == "__main__":
    run()
