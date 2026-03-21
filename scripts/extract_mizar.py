#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from Mizar Mathematical Library (MML) and convert to ECHIDNA
training format.

Attempts to download from the MML GitHub mirror. Falls back to generating
high-quality synthetic Mizar proofs.

Mizar is a formal language for writing mathematical proofs in a readable,
declarative style. The MML contains over 60,000 theorems across all areas
of mathematics.

Output: training_data/proof_states_mizar.jsonl
ID range: 94000+
"""

import json
import os
import re
import urllib.request
import urllib.error
from typing import Dict, List, Any, Tuple

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTERNAL_DIR = os.path.join(REPO_ROOT, "external_corpora", "mizar")
OUTPUT_DIR = os.path.join(REPO_ROOT, "training_data")
OUTPUT_FILE = os.path.join(OUTPUT_DIR, "proof_states_mizar.jsonl")
STATS_FILE = os.path.join(OUTPUT_DIR, "stats_mizar.json")
START_ID = 94000

# Mizar MML articles (some key ones)
MIZAR_RAW = "https://raw.githubusercontent.com/MizarProject/mml/master"
MIZAR_FILES = [
    "abcmiz_0.miz", "absvalue.miz", "algstr_0.miz", "arytm_0.miz",
    "arytm_1.miz", "arytm_3.miz", "binop_1.miz", "boole.miz",
    "card_1.miz", "complex1.miz", "enumset1.miz", "finseq_1.miz",
    "finset_1.miz", "funct_1.miz", "funct_2.miz", "group_1.miz",
    "int_1.miz", "lattices.miz", "membered.miz", "nat_1.miz",
    "numbers.miz", "ordinal1.miz", "orders_1.miz", "partfun1.miz",
    "pre_topc.miz", "prob_1.miz", "real_1.miz", "relat_1.miz",
    "relset_1.miz", "ring_1.miz", "seq_1.miz", "square_1.miz",
    "struct_0.miz", "subset_1.miz", "tops_1.miz", "tarski.miz",
    "topreal1.miz", "topsp_1.miz", "vectsp_1.miz", "xboole_0.miz",
    "xreal_0.miz", "zfmisc_1.miz",
]


def parse_mizar_file(filepath: str) -> List[Dict[str, Any]]:
    """
    Parse a Mizar .miz file and extract theorem/registration/definition blocks.

    Mizar proofs are structured as:
        theorem ThName:
          statement
        proof
          ...
        end;
    """
    results = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
    except OSError:
        return results

    # Pattern: theorem [Label:] statement proof ... end;
    thm_pattern = re.compile(
        r'theorem\s+(?:(\w+)\s*:)?\s*(.*?)\s*proof\s*(.*?)\s*end\s*;',
        re.DOTALL | re.IGNORECASE
    )
    for m in thm_pattern.finditer(content):
        label = m.group(1) or "anonymous"
        statement = re.sub(r'\s+', ' ', m.group(2).strip())[:300]
        proof_body = re.sub(r'\s+', ' ', m.group(3).strip())[:500]

        # Extract Mizar proof steps
        steps = re.findall(
            r'\b(assume|let|take|consider|thus|hence|suppose|per cases|set|reconsider|hereby)\b',
            proof_body, re.IGNORECASE
        )
        steps_unique = list(dict.fromkeys(s.lower() for s in steps))

        results.append({
            "theorem": label,
            "goal": statement,
            "tactic_proof": proof_body,
            "tactics": steps_unique,
            "source": f"mizar/{os.path.basename(filepath)}",
        })

    # Also extract registrations (important Mizar concept)
    reg_pattern = re.compile(
        r'registration\s*(.*?)\s*end\s*;',
        re.DOTALL | re.IGNORECASE
    )
    for i, m in enumerate(reg_pattern.finditer(content)):
        body = re.sub(r'\s+', ' ', m.group(1).strip())[:300]
        if body:
            results.append({
                "theorem": f"registration_{i}",
                "goal": body,
                "tactic_proof": "",
                "tactics": ["registration"],
                "source": f"mizar/{os.path.basename(filepath)}",
            })

    return results


def download_mizar_files() -> int:
    """Attempt to download Mizar MML articles."""
    downloaded = 0
    for fname in MIZAR_FILES:
        url = f"{MIZAR_RAW}/{fname}"
        local_path = os.path.join(EXTERNAL_DIR, fname)
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
            print(f"  Downloaded: {fname}")
        except (urllib.error.URLError, OSError, TimeoutError) as exc:
            print(f"  Skipped {fname}: {exc}")
    return downloaded


def generate_synthetic_mizar() -> List[Dict[str, Any]]:
    """
    Generate high-quality synthetic Mizar proofs.

    Mizar uses a structured, readable proof language with keywords like
    assume, let, take, consider, thus, hence, suppose, per cases,
    set, reconsider, hereby, thesis, and ... by reference.
    """
    set_theory = [
        ("union_comm", "for A, B being set holds A \\/ B = B \\/ A",
         "let A, B be set; thus A \\/ B = B \\/ A by XBOOLE_0:def 3;"),
        ("inter_comm", "for A, B being set holds A /\\ B = B /\\ A",
         "let A, B be set; thus A /\\ B = B /\\ A by XBOOLE_0:def 4;"),
        ("union_assoc", "for A, B, C being set holds A \\/ (B \\/ C) = (A \\/ B) \\/ C",
         "let A, B, C be set; thus thesis by XBOOLE_1:4;"),
        ("inter_assoc", "for A, B, C being set holds A /\\ (B /\\ C) = (A /\\ B) /\\ C",
         "let A, B, C be set; thus thesis by XBOOLE_1:16;"),
        ("union_empty", "for A being set holds A \\/ {} = A",
         "let A be set; thus thesis by XBOOLE_1:1;"),
        ("inter_univ", "for A being set holds A /\\ A = A",
         "let A be set; thus thesis by XBOOLE_1:17;"),
        ("subset_refl", "for A being set holds A c= A",
         "let A be set; let x be object; assume x in A; thus x in A;"),
        ("subset_trans", "for A, B, C being set st A c= B & B c= C holds A c= C",
         "let A, B, C be set; assume A1: A c= B; assume A2: B c= C; let x be object; assume x in A; then x in B by A1; hence x in C by A2;"),
        ("subset_union_left", "for A, B being set holds A c= A \\/ B",
         "let A, B be set; let x be object; assume x in A; hence x in A \\/ B by XBOOLE_0:def 3;"),
        ("subset_inter_left", "for A, B being set holds A /\\ B c= A",
         "let A, B be set; let x be object; assume x in A /\\ B; hence x in A by XBOOLE_0:def 4;"),
        ("de_morgan_union", "for A, B, X being set holds X \\ (A \\/ B) = (X \\ A) /\\ (X \\ B)",
         "let A, B, X be set; thus thesis by XBOOLE_1:53;"),
        ("de_morgan_inter", "for A, B, X being set holds X \\ (A /\\ B) = (X \\ A) \\/ (X \\ B)",
         "let A, B, X be set; thus thesis by XBOOLE_1:54;"),
        ("empty_subset", "for A being set holds {} c= A",
         "let A be set; thus {} c= A by XBOOLE_1:2;"),
        ("subset_antisym", "for A, B being set st A c= B & B c= A holds A = B",
         "let A, B be set; assume A c= B; assume B c= A; thus A = B by XBOOLE_0:def 10;"),
        ("power_set_member", "for A, B being set st A c= B holds A in bool B",
         "let A, B be set; assume A c= B; thus A in bool B by ZFMISC_1:def 1;"),
    ]

    natural_numbers = [
        ("nat_add_comm", "for m, n being Nat holds m + n = n + m",
         "let m, n be Nat; thus m + n = n + m by XCMPLX_0:def 3;"),
        ("nat_add_assoc", "for m, n, k being Nat holds (m + n) + k = m + (n + k)",
         "let m, n, k be Nat; thus (m + n) + k = m + (n + k) by XCMPLX_1:1;"),
        ("nat_mul_comm", "for m, n being Nat holds m * n = n * m",
         "let m, n be Nat; thus m * n = n * m by XCMPLX_0:def 4;"),
        ("nat_mul_assoc", "for m, n, k being Nat holds (m * n) * k = m * (n * k)",
         "let m, n, k be Nat; thus (m * n) * k = m * (n * k) by XCMPLX_1:4;"),
        ("nat_distrib", "for m, n, k being Nat holds m * (n + k) = m * n + m * k",
         "let m, n, k be Nat; thus m * (n + k) = m * n + m * k by XCMPLX_1:8;"),
        ("nat_add_zero", "for n being Nat holds n + 0 = n",
         "let n be Nat; thus n + 0 = n;"),
        ("nat_mul_zero", "for n being Nat holds n * 0 = 0",
         "let n be Nat; thus n * 0 = 0;"),
        ("nat_mul_one", "for n being Nat holds n * 1 = n",
         "let n be Nat; thus n * 1 = n;"),
        ("nat_le_refl", "for n being Nat holds n <= n",
         "let n be Nat; thus n <= n;"),
        ("nat_le_antisym", "for m, n being Nat st m <= n & n <= m holds m = n",
         "let m, n be Nat; assume A1: m <= n; assume A2: n <= m; thus m = n by A1, A2, XXREAL_0:1;"),
        ("nat_le_trans", "for m, n, k being Nat st m <= n & n <= k holds m <= k",
         "let m, n, k be Nat; assume m <= n; assume n <= k; hence m <= k by XXREAL_0:2;"),
        ("nat_lt_succ", "for n being Nat holds n < n + 1",
         "let n be Nat; thus n < n + 1 by NAT_1:13;"),
        ("nat_induction_schema", "for P being Nat-defined Function st P.0 is true & (for n being Nat st P.n is true holds P.(n+1) is true) holds for n being Nat holds P.n is true",
         "let P be Nat-defined Function; assume A1: P.0 is true; assume A2: for n being Nat st P.n is true holds P.(n+1) is true; defpred Q[Nat] means P.$1 is true; A3: Q[0] by A1; A4: for n being Nat st Q[n] holds Q[n+1] by A2; thus for n being Nat holds Q[n] from NAT_1:sch 2(A3, A4);"),
        ("nat_well_ordering", "for X being non empty Subset of NAT ex m being Nat st m in X & for n being Nat st n in X holds m <= n",
         "let X be non empty Subset of NAT; thus thesis by NAT_1:def 1;"),
        ("nat_div_mod", "for a being Nat, b being non zero Nat holds a = b * (a div b) + (a mod b)",
         "let a be Nat, b be non zero Nat; thus a = b * (a div b) + (a mod b) by NAT_D:def 1, NAT_D:def 2;"),
    ]

    real_numbers = [
        ("real_add_comm", "for x, y being Real holds x + y = y + x",
         "let x, y be Real; thus x + y = y + x by XCMPLX_0:def 3;"),
        ("real_mul_comm", "for x, y being Real holds x * y = y * x",
         "let x, y be Real; thus x * y = y * x by XCMPLX_0:def 4;"),
        ("real_add_inv", "for x being Real holds x + (-x) = 0",
         "let x be Real; thus x + (-x) = 0 by XCMPLX_0:def 6;"),
        ("real_mul_inv", "for x being non zero Real holds x * x\" = 1",
         "let x be non zero Real; thus x * x\" = 1 by XCMPLX_0:def 7;"),
        ("real_abs_nonneg", "for x being Real holds |.x.| >= 0",
         "let x be Real; thus |.x.| >= 0 by ABSVALUE:4;"),
        ("real_abs_zero", "for x being Real holds |.x.| = 0 iff x = 0",
         "let x be Real; thus |.x.| = 0 iff x = 0 by ABSVALUE:2;"),
        ("real_triangle", "for x, y being Real holds |.x + y.| <= |.x.| + |.y.|",
         "let x, y be Real; thus |.x + y.| <= |.x.| + |.y.| by ABSVALUE:13;"),
        ("real_sq_nonneg", "for x being Real holds x ^2 >= 0",
         "let x be Real; thus x ^2 >= 0 by XREAL_1:63;"),
        ("real_archimedes", "for x being positive Real ex n being Nat st x < n",
         "let x be positive Real; thus ex n being Nat st x < n by INT_1:37;"),
        ("real_complete", "for A being non empty bounded_above Subset of REAL ex s being Real st s is_least_upper_bound_of A",
         "let A be non empty bounded_above Subset of REAL; thus thesis by XXREAL_2:28;"),
    ]

    functions = [
        ("func_comp_assoc", "for f, g, h being Function st rng h c= dom g & rng g c= dom f holds (f * g) * h = f * (g * h)",
         "let f, g, h be Function; assume A1: rng h c= dom g; assume A2: rng g c= dom f; thus (f * g) * h = f * (g * h) by A1, A2, RELAT_1:36;"),
        ("func_id_comp", "for f being Function holds f * (id dom f) = f",
         "let f be Function; thus f * (id dom f) = f by FUNCT_1:22;"),
        ("func_injective_comp", "for f, g being Function st f is one-to-one & g is one-to-one & rng g c= dom f holds f * g is one-to-one",
         "let f, g be Function; assume A1: f is one-to-one; assume A2: g is one-to-one; assume A3: rng g c= dom f; thus f * g is one-to-one by A1, A2, A3, FUNCT_1:27;"),
        ("func_surjective_comp", "for f, g being Function st f is onto & g is onto holds f * g is onto",
         "let f, g be Function; assume f is onto; assume g is onto; thus f * g is onto by FUNCT_1:28;"),
        ("func_inverse", "for f being one-to-one Function holds f \" * f = id dom f",
         "let f be one-to-one Function; thus f \" * f = id dom f by FUNCT_1:44;"),
        ("func_image_union", "for f being Function, A, B being set holds f.:( A \\/ B) = f.:A \\/ f.:B",
         "let f be Function, A, B be set; thus f.:(A \\/ B) = f.:A \\/ f.:B by RELAT_1:120;"),
        ("func_image_inter_inj", "for f being one-to-one Function, A, B being set holds f.:(A /\\ B) = f.:A /\\ f.:B",
         "let f be one-to-one Function, A, B be set; thus f.:(A /\\ B) = f.:A /\\ f.:B by FUNCT_1:72;"),
        ("func_preimage_union", "for f being Function, A, B being set holds f\"(A \\/ B) = f\"A \\/ f\"B",
         "let f be Function, A, B be set; thus f\"(A \\/ B) = f\"A \\/ f\"B by RELAT_1:171;"),
    ]

    topology = [
        ("open_empty", "for T being TopSpace holds {} is open Subset of T",
         "let T be TopSpace; thus {} is open Subset of T by PRE_TOPC:def 2;"),
        ("open_carrier", "for T being TopSpace holds [#]T is open Subset of T",
         "let T be TopSpace; thus [#]T is open Subset of T by PRE_TOPC:def 2;"),
        ("open_union", "for T being TopSpace, F being Subset-Family of T st for A being Subset of T st A in F holds A is open holds union F is open Subset of T",
         "let T be TopSpace; let F be Subset-Family of T; assume for A being Subset of T st A in F holds A is open; thus union F is open Subset of T by PRE_TOPC:def 2;"),
        ("closed_empty", "for T being TopSpace holds {} is closed Subset of T",
         "let T be TopSpace; thus {} is closed Subset of T by PRE_TOPC:3;"),
        ("closed_carrier", "for T being TopSpace holds [#]T is closed Subset of T",
         "let T be TopSpace; thus [#]T is closed Subset of T by PRE_TOPC:3;"),
        ("closure_subset", "for T being TopSpace, A being Subset of T holds A c= Cl A",
         "let T be TopSpace, A be Subset of T; thus A c= Cl A by PRE_TOPC:18;"),
        ("closure_closed", "for T being TopSpace, A being Subset of T holds Cl A is closed",
         "let T be TopSpace, A be Subset of T; thus Cl A is closed by PRE_TOPC:def 6;"),
        ("continuous_preimage_open", "for f being continuous Function of T1, T2, V being open Subset of T2 holds f\"V is open Subset of T1",
         "let f be continuous Function of T1, T2; let V be open Subset of T2; thus f\"V is open Subset of T1 by TOPS_2:43;"),
        ("compact_closed_subset", "for T being compact TopSpace, A being closed Subset of T holds A is compact",
         "let T be compact TopSpace; let A be closed Subset of T; thus A is compact by COMPTS_1:8;"),
        ("connected_image", "for f being continuous Function of T1, T2 st T1 is connected holds f.:[#]T1 is connected Subset of T2",
         "let f be continuous Function of T1, T2; assume T1 is connected; thus f.:[#]T1 is connected Subset of T2 by CONNSP_1:15;"),
    ]

    algebra = [
        ("group_id_unique", "for G being Group holds for e1, e2 being Element of G st (for a being Element of G holds e1 * a = a & a * e1 = a) & (for a being Element of G holds e2 * a = a & a * e2 = a) holds e1 = e2",
         "let G be Group; let e1, e2 be Element of G; assume A1: for a being Element of G holds e1 * a = a & a * e1 = a; assume A2: for a being Element of G holds e2 * a = a & a * e2 = a; thus e1 = e1 * e2 by A2 .= e2 by A1;"),
        ("group_inv_unique", "for G being Group, a, b1, b2 being Element of G st a * b1 = 1_G & a * b2 = 1_G holds b1 = b2",
         "let G be Group; let a, b1, b2 be Element of G; assume A1: a * b1 = 1_G; assume A2: a * b2 = 1_G; thus b1 = (a\") * a * b1 by GROUP_1:def 5 .= (a\") * (a * b1) by GROUP_1:def 3 .= (a\") * 1_G by A1 .= a\" by GROUP_1:def 4 .= (a\") * (a * b2) by A2 .= (a\") * a * b2 by GROUP_1:def 3 .= 1_G * b2 by GROUP_1:def 5 .= b2 by GROUP_1:def 4;"),
        ("group_inv_inv", "for G being Group, a being Element of G holds (a\")\" = a",
         "let G be Group; let a be Element of G; thus (a\")\" = a by GROUP_1:8;"),
        ("group_inv_prod", "for G being Group, a, b being Element of G holds (a * b)\" = b\" * a\"",
         "let G be Group; let a, b be Element of G; thus (a * b)\" = b\" * a\" by GROUP_1:17;"),
        ("subgroup_criterion", "for G being Group, H being non empty Subset of G st (for a, b being Element of G st a in H & b in H holds a * b\" in H) holds H is Subgroup of G",
         "let G be Group; let H be non empty Subset of G; assume for a, b being Element of G st a in H & b in H holds a * b\" in H; thus H is Subgroup of G by GROUP_2:52;"),
        ("ring_add_comm", "for R being Ring, a, b being Element of R holds a + b = b + a",
         "let R be Ring; let a, b be Element of R; thus a + b = b + a by RLVECT_1:2;"),
        ("ring_mul_assoc", "for R being Ring, a, b, c being Element of R holds (a * b) * c = a * (b * c)",
         "let R be Ring; let a, b, c be Element of R; thus (a * b) * c = a * (b * c) by GROUP_1:def 3;"),
        ("ring_distrib_left", "for R being Ring, a, b, c being Element of R holds a * (b + c) = a * b + a * c",
         "let R be Ring; let a, b, c be Element of R; thus a * (b + c) = a * b + a * c by VECTSP_1:def 7;"),
    ]

    all_categories = [
        ("set_theory", set_theory),
        ("natural_numbers", natural_numbers),
        ("real_numbers", real_numbers),
        ("functions", functions),
        ("topology", topology),
        ("algebra", algebra),
    ]

    proofs = []
    for category, theorems in all_categories:
        for name, goal, proof_body in theorems:
            steps = re.findall(
                r'\b(assume|let|take|consider|thus|hence|suppose|per cases|set|reconsider|hereby|defpred)\b',
                proof_body, re.IGNORECASE
            )
            proofs.append({
                "theorem": name,
                "goal": f"theorem {name}: {goal}",
                "tactic_proof": f"proof {proof_body} end;",
                "tactics": list(dict.fromkeys(s.lower() for s in steps))[:20],
                "source": f"mizar_synthetic/{category}",
            })
    return proofs


def run() -> Tuple[int, int]:
    """Run the full extraction pipeline."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(EXTERNAL_DIR, exist_ok=True)

    all_entries: List[Dict[str, Any]] = []
    extracted_count = 0

    print("[Mizar] Phase 1: Attempting to download MML articles ...")
    downloaded = download_mizar_files()
    print(f"  Downloaded/cached {downloaded} files")

    for fname in os.listdir(EXTERNAL_DIR):
        if fname.endswith(".miz"):
            fpath = os.path.join(EXTERNAL_DIR, fname)
            parsed = parse_mizar_file(fpath)
            for entry in parsed:
                all_entries.append(entry)
            if parsed:
                print(f"  Parsed {len(parsed)} theorems from {fname}")
    extracted_count = len(all_entries)

    print(f"[Mizar] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_mizar()
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
            "prover": "Mizar",
            "theorem": entry["theorem"],
            "goal": entry["goal"],
            "context": entry.get("tactics", []),
            "tactic_proof": entry.get("tactic_proof", ""),
            "source": entry.get("source", "mizar"),
        }
        output_records.append(record)
        current_id += 1

    with open(OUTPUT_FILE, "w", encoding="utf-8") as fh:
        for rec in output_records:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    stats = {
        "prover": "Mizar",
        "total_proofs": len(output_records),
        "extracted_from_source": extracted_count,
        "synthetic_added": len(output_records) - extracted_count,
        "id_range": [START_ID, current_id - 1],
        "output_file": OUTPUT_FILE,
    }
    with open(STATS_FILE, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2)

    print(f"\n[Mizar] COMPLETE: {len(output_records)} proofs written to {OUTPUT_FILE}")
    print(f"  Extracted from source: {extracted_count}")
    print(f"  Synthetic: {len(output_records) - extracted_count}")
    return extracted_count, len(output_records) - extracted_count


if __name__ == "__main__":
    run()
