import sys

variants = [
    "Agda", "Coq", "Lean", "Isabelle", "Z3", "CVC5", "Metamath", "HOLLight", "Mizar", "PVS", "ACL2", "HOL4",
    "Idris2", "Lean3", "Vampire", "EProver", "SPASS", "AltErgo", "FStar", "Dafny", "Why3", "TLAPS", "Twelf",
    "Nuprl", "Minlog", "Imandra", "GLPK", "SCIP", "MiniZinc", "Chuffed", "ORTools", "TypedWasm", "SPIN",
    "CBMC", "SeaHorn", "CaDiCaL", "Kissat", "MiniSat", "NuSMV", "TLC", "Alloy", "Prism", "UPPAAL", "FramaC",
    "Viper", "Tamarin", "ProVerif", "KeY", "DReal", "ABC", "TypeLL", "KatagoriaVerifier", "TropicalTypeChecker",
    "ChoreographicTypeChecker", "EpistemicTypeChecker", "EchoTypeChecker", "SessionTypeChecker", "ModalTypeChecker",
    "QTTTypeChecker", "EffectRowTypeChecker", "DependentTypeChecker", "RefinementTypeChecker", "OrdinaryTypeChecker",
    "PhantomTypeChecker", "PolymorphicTypeChecker", "ExistentialTypeChecker", "HigherKindedTypeChecker",
    "RowTypeChecker", "SubtypingTypeChecker", "IntersectionTypeChecker", "UnionTypeChecker", "GradualTypeChecker",
    "HoareTypeChecker", "IndexedTypeChecker", "LinearTypeChecker", "AffineTypeChecker", "RelevantTypeChecker",
    "OrderedTypeChecker", "UniquenessTypeChecker", "ImmutableTypeChecker", "CapabilityTypeChecker",
    "BunchedTypeChecker", "TemporalTypeChecker", "ProvabilityTypeChecker", "ImpureTypeChecker", "CoeffectTypeChecker",
    "ProbabilisticTypeChecker", "DyadicTypeChecker", "HomotopyTypeChecker", "CubicalTypeChecker",
    "NominalTypeChecker", "Abella", "Dedukti", "Cameleer", "ACL2s", "IsabelleZF", "Boogie", "Naproche",
    "Matita", "Arend", "Athena", "LambdaProlog", "Mercury", "Nitpick", "Nunchaku"
]

def generate_idr():
    out = []
    out.append("-- SPDX-License-Identifier: PMPL-1.0-or-later")
    out.append("-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>")
    out.append("--")
    out.append("-- ProverKindInjectivity.idr")
    out.append("--")
    out.append("-- Proves that the kind_to_u8 mapping from ProverKind to Nat is injective:")
    out.append("-- no two distinct prover variants share the same numeric discriminant.")
    out.append("-- This guarantees collision-free serialisation and dispatch.")
    out.append("--")
    out.append(f"-- Models all {len(variants)} ProverKind variants from src/rust/provers/mod.rs.")
    out.append("--")
    out.append("-- Uses %default total to enforce totality on every definition.")
    out.append("")
    out.append("module ProverKindInjectivity")
    out.append("")
    out.append("import Data.Nat")
    out.append("")
    out.append("%default total")
    out.append("")
    out.append("-- ==========================================================================")
    out.append(f"-- Section 1: ProverKind -- all {len(variants)} variants")
    out.append("-- ==========================================================================")
    out.append("")
    out.append(f"||| All {len(variants)} prover backends supported by Echidna, mirroring")
    out.append("||| the ProverKind enum in src/rust/provers/mod.rs.")
    out.append("public export")
    out.append("data ProverKind : Type where")
    for v in variants:
        out.append(f"  {v:<24} : ProverKind")
    out.append("")
    out.append("-- ==========================================================================")
    out.append("-- Section 2: kind_to_u8 mapping")
    out.append("-- ==========================================================================")
    out.append("")
    out.append(f"||| Maps each ProverKind to a unique Nat discriminant (0-{len(variants)-1}).")
    out.append("||| This mirrors the implicit Rust enum discriminant ordering.")
    out.append("public export")
    out.append("kindToU8 : ProverKind -> Nat")
    for i, v in enumerate(variants):
        out.append(f"kindToU8 {v:<24} = {i}")
    out.append("")
    out.append("-- ==========================================================================")
    out.append("-- Section 3: Inverse mapping (u8 -> ProverKind)")
    out.append("-- ==========================================================================")
    out.append("")
    out.append(f"||| Inverse of kindToU8.  Returns Nothing for values outside [0, {len(variants)-1}].")
    out.append("public export")
    out.append("u8ToKind : Nat -> Maybe ProverKind")
    for i, v in enumerate(variants):
        out.append(f"u8ToKind {i:<3} = Just {v}")
    out.append("u8ToKind _   = Nothing")
    out.append("")
    out.append("-- ==========================================================================")
    out.append("-- Section 4: Round-trip proof (u8ToKind . kindToU8 = Just)")
    out.append("-- ==========================================================================")
    out.append("")
    out.append("||| Round-trip: u8ToKind (kindToU8 k) = Just k for all k.")
    out.append("public export")
    out.append("roundTrip : (k : ProverKind) -> u8ToKind (kindToU8 k) = Just k")
    for v in variants:
        out.append(f"roundTrip {v:<24} = Refl")
    out.append("")
    out.append("-- ==========================================================================")
    out.append("-- Section 5: Injectivity proof (kindToU8 a = kindToU8 b -> a = b)")
    out.append("-- ==========================================================================")
    out.append("")
    out.append("public export")
    out.append("kindToU8Injective : (a, b : ProverKind) -> kindToU8 a = kindToU8 b -> a = b")
    out.append("kindToU8Injective a b prf =")
    out.append("  let leftRoundTrip  = roundTrip a")
    out.append("      rightRoundTrip = roundTrip b")
    out.append("      step1 = replace {p = \\x => u8ToKind x = Just a} prf leftRoundTrip")
    out.append("      justEq = trans (sym step1) rightRoundTrip")
    out.append("  in justInjective justEq")
    out.append("  where")
    out.append("    justInjective : {0 x, y : t} -> Just x = Just y -> x = y")
    out.append("    justInjective Refl = Refl")
    out.append("")
    out.append("-- ==========================================================================")
    out.append("-- Section 6: Variant count witness")
    out.append("-- ==========================================================================")
    out.append("")
    out.append("public export")
    out.append("proverKindCount : Nat")
    out.append(f"proverKindCount = {len(variants)}")
    out.append("")
    out.append("public export")
    out.append("maxDiscriminant : Nat")
    out.append(f"maxDiscriminant = {len(variants)-1}")
    out.append("")
    out.append(f"||| Every discriminant is within the valid range [0, {len(variants)-1}].")
    out.append(f"public export")
    out.append(f"discriminantBounded : (k : ProverKind) -> LTE (kindToU8 k) {len(variants)-1}")
    for i, v in enumerate(variants):
        if i == 0:
            out.append(f"discriminantBounded {v:<24} = LTEZero")
        else:
            s = "LTESucc (" * i + "LTEZero" + ")" * i
            out.append(f"discriminantBounded {v:<24} = {s}")
    return "\n".join(out)

if __name__ == "__main__":
    print(generate_idr())
