#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Extract proofs from Idris2 stdlib and tests, convert to ECHIDNA training format.

Attempts to download from the Idris2 GitHub repository (libs/ and tests/ dirs).
Falls back to generating high-quality synthetic Idris2 proofs.

Idris2 is a dependently-typed functional programming language with first-class
support for theorem proving. It features linear types (Quantities) and an
elaborator reflection system for metaprogramming.

Output: training_data/proof_states_idris2.jsonl
ID range: 98000+
"""

import json
import os
import re
import urllib.request
import urllib.error
from typing import Dict, List, Any, Tuple

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXTERNAL_DIR = os.path.join(REPO_ROOT, "external_corpora", "idris2")
OUTPUT_DIR = os.path.join(REPO_ROOT, "training_data")
OUTPUT_FILE = os.path.join(OUTPUT_DIR, "proof_states_idris2.jsonl")
STATS_FILE = os.path.join(OUTPUT_DIR, "stats_idris2.json")
START_ID = 98000

IDRIS2_RAW = "https://raw.githubusercontent.com/idris-lang/Idris2/main"
IDRIS2_FILES = [
    "libs/prelude/Prelude/Types.idr",
    "libs/prelude/Prelude/Basics.idr",
    "libs/prelude/Prelude/EqOrd.idr",
    "libs/prelude/Prelude/Interfaces.idr",
    "libs/prelude/Prelude/Num.idr",
    "libs/base/Data/List.idr",
    "libs/base/Data/Nat.idr",
    "libs/base/Data/Vect.idr",
    "libs/base/Data/Fin.idr",
    "libs/base/Data/SnocList.idr",
    "libs/base/Decidable/Equality.idr",
    "libs/contrib/Data/Nat/Factor.idr",
    "libs/contrib/Data/List/Elem.idr",
    "libs/contrib/Data/Vect/Sort.idr",
    "tests/idris2/basic/basic001/Test.idr",
    "tests/idris2/basic/basic002/Test.idr",
]


def parse_idris2_file(filepath: str) -> List[Dict[str, Any]]:
    """Parse an Idris2 .idr file and extract public export function/data patterns."""
    results = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
    except OSError:
        return results

    # Type signature followed by implementation
    # Pattern: name : type\nname args = body
    sig_pattern = re.compile(
        r'^(\w+)\s*:\s*(.*?)$',
        re.MULTILINE
    )

    for m in sig_pattern.finditer(content):
        name = m.group(1).strip()
        sig = re.sub(r'\s+', ' ', m.group(2).strip())[:300]

        # Skip imports, module declarations, etc.
        if name in ('module', 'import', 'data', 'record', 'interface', 'implementation', 'where', 'namespace', 'mutual', 'parameters'):
            continue

        # Look for proof-relevant types
        if any(kw in sig for kw in ['Void', 'Dec', 'Equal', 'So', 'LTE', 'GTE', 'Elem', 'contra', 'Refl', 'DecEq', 'Uninhabited']):
            keywords = re.findall(r'\b(Void|Dec|Equal|So|LTE|GTE|Elem|Refl|DecEq|Uninhabited|Vect|Nat|Fin|DPair|Not)\b', sig)
            results.append({
                "theorem": name,
                "goal": sig,
                "tactics": list(dict.fromkeys(keywords))[:20],
                "source": f"idris2/{os.path.basename(filepath)}",
            })

    return results


def download_idris2_files() -> int:
    """Attempt to download Idris2 source files."""
    downloaded = 0
    for rel_path in IDRIS2_FILES:
        url = f"{IDRIS2_RAW}/{rel_path}"
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


def generate_synthetic_idris2() -> List[Dict[str, Any]]:
    """Generate high-quality synthetic Idris2 proofs using dependent types."""

    equality_proofs = [
        ("plusZeroRightNeutral", "plusZeroRightNeutral : (n : Nat) -> n + 0 = n", "plusZeroRightNeutral Z = Refl\nplusZeroRightNeutral (S k) = cong S (plusZeroRightNeutral k)"),
        ("plusSuccRightSucc", "plusSuccRightSucc : (left : Nat) -> (right : Nat) -> S (left + right) = left + S right", "plusSuccRightSucc Z right = Refl\nplusSuccRightSucc (S k) right = cong S (plusSuccRightSucc k right)"),
        ("plusCommutative", "plusCommutative : (left : Nat) -> (right : Nat) -> left + right = right + left", "plusCommutative Z right = sym (plusZeroRightNeutral right)\nplusCommutative (S k) right = rewrite plusCommutative k right in plusSuccRightSucc right k"),
        ("plusAssociative", "plusAssociative : (l, c, r : Nat) -> l + (c + r) = (l + c) + r", "plusAssociative Z c r = Refl\nplusAssociative (S k) c r = cong S (plusAssociative k c r)"),
        ("multZeroRightZero", "multZeroRightZero : (n : Nat) -> n * 0 = 0", "multZeroRightZero Z = Refl\nmultZeroRightZero (S k) = multZeroRightZero k"),
        ("multOneRightNeutral", "multOneRightNeutral : (n : Nat) -> n * 1 = n", "multOneRightNeutral Z = Refl\nmultOneRightNeutral (S k) = cong S (multOneRightNeutral k)"),
        ("multRightSuccPlus", "multRightSuccPlus : (left, right : Nat) -> left * S right = left + left * right", "multRightSuccPlus Z right = Refl\nmultRightSuccPlus (S k) right = rewrite multRightSuccPlus k right in rewrite sym (plusAssociative right k (k * right)) in rewrite plusCommutative right k in rewrite plusAssociative k right (k * right) in Refl"),
        ("multCommutative", "multCommutative : (left, right : Nat) -> left * right = right * left", "multCommutative Z right = sym (multZeroRightZero right)\nmultCommutative (S k) right = rewrite multCommutative k right in sym (multRightSuccPlus right k)"),
        ("multDistributesOverPlusLeft", "multDistributesOverPlusLeft : (l, c, r : Nat) -> (l + c) * r = l * r + c * r", "multDistributesOverPlusLeft Z c r = Refl\nmultDistributesOverPlusLeft (S k) c r = rewrite multDistributesOverPlusLeft k c r in sym (plusAssociative r (k * r) (c * r))"),
        ("multAssociative", "multAssociative : (l, c, r : Nat) -> l * (c * r) = (l * c) * r", "multAssociative Z c r = Refl\nmultAssociative (S k) c r = rewrite multAssociative k c r in rewrite multDistributesOverPlusLeft c (k * c) r in Refl"),
    ]

    decidable = [
        ("decEqNat", "decEqNat : (n1, n2 : Nat) -> Dec (n1 = n2)", "decEqNat Z Z = Yes Refl\ndecEqNat Z (S _) = No absurd\ndecEqNat (S _) Z = No absurd\ndecEqNat (S k) (S j) = case decEqNat k j of { Yes prf => Yes (cong S prf); No contra => No (\\h => contra (injective h)) }"),
        ("isLTE", "isLTE : (m, n : Nat) -> Dec (LTE m n)", "isLTE Z n = Yes LTEZero\nisLTE (S k) Z = No absurd\nisLTE (S k) (S j) = case isLTE k j of { Yes prf => Yes (LTESucc prf); No contra => No (\\(LTESucc p) => contra p) }"),
        ("decEqBool", "decEqBool : (b1, b2 : Bool) -> Dec (b1 = b2)", "decEqBool True True = Yes Refl\ndecEqBool False False = Yes Refl\ndecEqBool True False = No absurd\ndecEqBool False True = No absurd"),
        ("notNotTrue", "notNotTrue : Not (Not a) -> a -> Void -> Void", "notNotTrue f x = f (\\y => absurd (y x))"),
        ("decNot", "decNot : Dec a -> Dec (Not a)", "decNot (Yes prf) = No (\\f => f prf)\ndecNot (No contra) = Yes contra"),
    ]

    vector_proofs = [
        ("vectAppendNilRightNeutral", "vectAppendNilRightNeutral : (xs : Vect n a) -> xs ++ [] = xs", "vectAppendNilRightNeutral [] = Refl\nvectAppendNilRightNeutral (x :: xs) = cong (x ::) (vectAppendNilRightNeutral xs)"),
        ("vectMapId", "vectMapId : (xs : Vect n a) -> map id xs = xs", "vectMapId [] = Refl\nvectMapId (x :: xs) = cong (x ::) (vectMapId xs)"),
        ("vectMapCompose", "vectMapCompose : (f : b -> c) -> (g : a -> b) -> (xs : Vect n a) -> map f (map g xs) = map (f . g) xs", "vectMapCompose f g [] = Refl\nvectMapCompose f g (x :: xs) = cong (f (g x) ::) (vectMapCompose f g xs)"),
        ("vectLengthMap", "vectLengthMap : (f : a -> b) -> (xs : Vect n a) -> length (map f xs) = length xs", "vectLengthMap f [] = Refl\nvectLengthMap f (x :: xs) = cong S (vectLengthMap f xs)"),
        ("vectReverseReverse", "vectReverseReverse : (xs : Vect n a) -> reverse (reverse xs) = xs", ""),
        ("vectIndexMap", "vectIndexMap : (f : a -> b) -> (xs : Vect n a) -> (i : Fin n) -> index i (map f xs) = f (index i xs)", "vectIndexMap f (x :: xs) FZ = Refl\nvectIndexMap f (x :: xs) (FS k) = vectIndexMap f xs k"),
        ("vectZipWithComm", "vectZipWithComm : (f : a -> a -> b) -> ((x, y : a) -> f x y = f y x) -> (xs, ys : Vect n a) -> zipWith f xs ys = zipWith f ys xs", "vectZipWithComm f prf [] [] = Refl\nvectZipWithComm f prf (x :: xs) (y :: ys) = rewrite prf x y in cong (f y x ::) (vectZipWithComm f prf xs ys)"),
        ("vectAppendLength", "vectAppendLength : (xs : Vect m a) -> (ys : Vect n a) -> length (xs ++ ys) = m + n", "vectAppendLength [] ys = Refl\nvectAppendLength (x :: xs) ys = cong S (vectAppendLength xs ys)"),
    ]

    list_proofs = [
        ("appendNilRightNeutral", "appendNilRightNeutral : (l : List a) -> l ++ [] = l", "appendNilRightNeutral [] = Refl\nappendNilRightNeutral (x :: xs) = cong (x ::) (appendNilRightNeutral xs)"),
        ("appendAssociative", "appendAssociative : (l, c, r : List a) -> l ++ (c ++ r) = (l ++ c) ++ r", "appendAssociative [] c r = Refl\nappendAssociative (x :: xs) c r = cong (x ::) (appendAssociative xs c r)"),
        ("mapAppend", "mapAppend : (f : a -> b) -> (l1, l2 : List a) -> map f (l1 ++ l2) = map f l1 ++ map f l2", "mapAppend f [] l2 = Refl\nmapAppend f (x :: xs) l2 = cong (f x ::) (mapAppend f xs l2)"),
        ("lengthAppend", "lengthAppend : (l1, l2 : List a) -> length (l1 ++ l2) = length l1 + length l2", "lengthAppend [] l2 = Refl\nlengthAppend (x :: xs) l2 = cong S (lengthAppend xs l2)"),
        ("mapId", "mapId : (l : List a) -> map id l = l", "mapId [] = Refl\nmapId (x :: xs) = cong (x ::) (mapId xs)"),
        ("mapCompose", "mapCompose : (f : b -> c) -> (g : a -> b) -> (l : List a) -> map f (map g l) = map (f . g) l", "mapCompose f g [] = Refl\nmapCompose f g (x :: xs) = cong (f (g x) ::) (mapCompose f g xs)"),
        ("filterAppend", "filterAppend : (p : a -> Bool) -> (l1, l2 : List a) -> filter p (l1 ++ l2) = filter p l1 ++ filter p l2", "filterAppend p [] l2 = Refl\nfilterAppend p (x :: xs) l2 with (p x) | filterAppend p xs l2\n  _ | True  | rec = cong (x ::) rec\n  _ | False | rec = rec"),
        ("reverseAppend", "reverseAppend : (l1, l2 : List a) -> reverse (l1 ++ l2) = reverse l2 ++ reverse l1", ""),
    ]

    fin_proofs = [
        ("finToNatBound", "finToNatBound : (i : Fin n) -> LT (finToNat i) n", "finToNatBound FZ = LTESucc LTEZero\nfinToNatBound (FS k) = LTESucc (finToNatBound k)"),
        ("finToNatWeaken", "finToNatWeaken : (i : Fin n) -> finToNat (weaken i) = finToNat i", "finToNatWeaken FZ = Refl\nfinToNatWeaken (FS k) = cong S (finToNatWeaken k)"),
        ("finToNatLast", "finToNatLast : {n : Nat} -> finToNat (last {n}) = n", "finToNatLast {n = Z} = Refl\nfinToNatLast {n = S k} = cong S finToNatLast"),
        ("strengthenWeaken", "strengthenWeaken : (i : Fin n) -> strengthen (weaken i) = Just i", ""),
        ("lastIsLargest", "lastIsLargest : (i : Fin (S n)) -> LTE (finToNat i) n", ""),
    ]

    linear_types = [
        ("linearSwap", "linearSwap : (1 x : a) -> (1 y : b) -> (b, a)", "linearSwap x y = (y, x)"),
        ("linearDup", "linearDup : (1 x : a) -> {auto prf : Dup a} -> (a, a)", "linearDup x = dup x"),
        ("linearMap", "linearMap : (1 f : a -o b) -> (1 xs : LList a) -> LList b", "linearMap f [] = []\nlinearMap f (x :: xs) = f x :: linearMap f xs"),
        ("useOnce", "useOnce : (1 r : Resource) -> IO ()", "useOnce r = release r"),
        ("linearFold", "linearFold : (1 f : b -o a -o b) -> (1 init : b) -> (1 xs : LList a) -> b", "linearFold f init [] = init\nlinearFold f init (x :: xs) = linearFold f (f init x) xs"),
    ]

    dependent_pairs = [
        ("dpairFst", "dpairFst : DPair a p -> a", "dpairFst (x ** _) = x"),
        ("dpairSnd", "dpairSnd : (d : DPair a p) -> p (fst d)", "dpairSnd (_ ** prf) = prf"),
        ("filterDPair", "filterDPair : (p : a -> Bool) -> List a -> List (DPair a (\\x => So (p x)))", "filterDPair p [] = []\nfilterDPair p (x :: xs) with (p x) proof eq\n  _ | True = (x ** eqToSo eq) :: filterDPair p xs\n  _ | False = filterDPair p xs"),
        ("lookupDPair", "lookupDPair : DecEq k => (key : k) -> List (k, v) -> Maybe (DPair v (\\_ => Unit))", ""),
        ("existsNat", "existsNat : (n : Nat ** LTE 5 n)", "existsNat = (5 ** reflexive)"),
    ]

    interfaces = [
        ("functorId", "functorId : Functor f => (x : f a) -> map id x = x", ""),
        ("functorCompose", "functorCompose : Functor f => (g : b -> c) -> (h : a -> b) -> (x : f a) -> map g (map h x) = map (g . h) x", ""),
        ("monadLeftId", "monadLeftId : Monad m => (a : t) -> (f : t -> m u) -> (pure a >>= f) = f a", ""),
        ("monadRightId", "monadRightId : Monad m => (ma : m a) -> (ma >>= pure) = ma", ""),
        ("monadAssoc", "monadAssoc : Monad m => (ma : m a) -> (f : a -> m b) -> (g : b -> m c) -> ((ma >>= f) >>= g) = (ma >>= (\\x => f x >>= g))", ""),
    ]

    all_categories = [
        ("equality", equality_proofs),
        ("decidable", decidable),
        ("vectors", vector_proofs),
        ("lists", list_proofs),
        ("fin", fin_proofs),
        ("linear", linear_types),
        ("dpair", dependent_pairs),
        ("interfaces", interfaces),
    ]

    proofs = []
    for category, entries in all_categories:
        for entry in entries:
            name = entry[0]
            sig = entry[1]
            impl = entry[2] if len(entry) > 2 else ""

            keywords = re.findall(r'\b(Vect|Nat|Fin|Dec|LTE|GTE|DPair|Refl|Void|So|Equal|List|Bool|Maybe|IO)\b', sig)
            proofs.append({
                "theorem": name,
                "goal": sig,
                "tactic_proof": impl,
                "tactics": list(dict.fromkeys(keywords))[:20],
                "source": f"idris2_synthetic/{category}",
            })
    return proofs


def run() -> Tuple[int, int]:
    """Run the full extraction pipeline."""
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs(EXTERNAL_DIR, exist_ok=True)

    all_entries: List[Dict[str, Any]] = []
    extracted_count = 0

    print("[Idris2] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_idris2_files()
    print(f"  Downloaded/cached {downloaded} files")

    for fname in os.listdir(EXTERNAL_DIR):
        if fname.endswith(".idr"):
            fpath = os.path.join(EXTERNAL_DIR, fname)
            parsed = parse_idris2_file(fpath)
            for entry in parsed:
                all_entries.append(entry)
            if parsed:
                print(f"  Parsed {len(parsed)} from {fname}")
    extracted_count = len(all_entries)

    print(f"[Idris2] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_idris2()
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
            "prover": "Idris2",
            "theorem": entry["theorem"],
            "goal": entry["goal"],
            "context": entry.get("tactics", []),
            "tactic_proof": entry.get("tactic_proof", ""),
            "source": entry.get("source", "idris2"),
        }
        output_records.append(record)
        current_id += 1

    with open(OUTPUT_FILE, "w", encoding="utf-8") as fh:
        for rec in output_records:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    stats = {
        "prover": "Idris2",
        "total_proofs": len(output_records),
        "extracted_from_source": extracted_count,
        "synthetic_added": len(output_records) - extracted_count,
        "id_range": [START_ID, current_id - 1],
    }
    with open(STATS_FILE, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=2)

    print(f"\n[Idris2] COMPLETE: {len(output_records)} proofs written to {OUTPUT_FILE}")
    return extracted_count, len(output_records) - extracted_count


if __name__ == "__main__":
    run()
