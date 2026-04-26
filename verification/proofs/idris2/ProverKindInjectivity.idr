-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ProverKindInjectivity.idr
--
-- Proves that the kind_to_u8 mapping from ProverKind to Nat is injective:
-- no two distinct prover variants share the same numeric discriminant.
-- This guarantees collision-free serialisation and dispatch.
--
-- Models all 105 ProverKind variants from src/rust/provers/mod.rs.
--
-- Uses %default total to enforce totality on every definition.

module ProverKindInjectivity

import Data.Nat

%default total

-- ==========================================================================
-- Section 1: ProverKind -- all 105 variants
-- ==========================================================================

||| All 105 prover backends supported by Echidna, mirroring
||| the ProverKind enum in src/rust/provers/mod.rs.
public export
data ProverKind : Type where
  Agda                     : ProverKind
  Coq                      : ProverKind
  Lean                     : ProverKind
  Isabelle                 : ProverKind
  Z3                       : ProverKind
  CVC5                     : ProverKind
  Metamath                 : ProverKind
  HOLLight                 : ProverKind
  Mizar                    : ProverKind
  PVS                      : ProverKind
  ACL2                     : ProverKind
  HOL4                     : ProverKind
  Idris2                   : ProverKind
  Lean3                    : ProverKind
  Vampire                  : ProverKind
  EProver                  : ProverKind
  SPASS                    : ProverKind
  AltErgo                  : ProverKind
  FStar                    : ProverKind
  Dafny                    : ProverKind
  Why3                     : ProverKind
  TLAPS                    : ProverKind
  Twelf                    : ProverKind
  Nuprl                    : ProverKind
  Minlog                   : ProverKind
  Imandra                  : ProverKind
  GLPK                     : ProverKind
  SCIP                     : ProverKind
  MiniZinc                 : ProverKind
  Chuffed                  : ProverKind
  ORTools                  : ProverKind
  TypedWasm                : ProverKind
  SPIN                     : ProverKind
  CBMC                     : ProverKind
  SeaHorn                  : ProverKind
  CaDiCaL                  : ProverKind
  Kissat                   : ProverKind
  MiniSat                  : ProverKind
  NuSMV                    : ProverKind
  TLC                      : ProverKind
  Alloy                    : ProverKind
  Prism                    : ProverKind
  UPPAAL                   : ProverKind
  FramaC                   : ProverKind
  Viper                    : ProverKind
  Tamarin                  : ProverKind
  ProVerif                 : ProverKind
  KeY                      : ProverKind
  DReal                    : ProverKind
  ABC                      : ProverKind
  TypeLL                   : ProverKind
  KatagoriaVerifier        : ProverKind
  TropicalTypeChecker      : ProverKind
  ChoreographicTypeChecker : ProverKind
  EpistemicTypeChecker     : ProverKind
  EchoTypeChecker          : ProverKind
  SessionTypeChecker       : ProverKind
  ModalTypeChecker         : ProverKind
  QTTTypeChecker           : ProverKind
  EffectRowTypeChecker     : ProverKind
  DependentTypeChecker     : ProverKind
  RefinementTypeChecker    : ProverKind
  OrdinaryTypeChecker      : ProverKind
  PhantomTypeChecker       : ProverKind
  PolymorphicTypeChecker   : ProverKind
  ExistentialTypeChecker   : ProverKind
  HigherKindedTypeChecker  : ProverKind
  RowTypeChecker           : ProverKind
  SubtypingTypeChecker     : ProverKind
  IntersectionTypeChecker  : ProverKind
  UnionTypeChecker         : ProverKind
  GradualTypeChecker       : ProverKind
  HoareTypeChecker         : ProverKind
  IndexedTypeChecker       : ProverKind
  LinearTypeChecker        : ProverKind
  AffineTypeChecker        : ProverKind
  RelevantTypeChecker      : ProverKind
  OrderedTypeChecker       : ProverKind
  UniquenessTypeChecker    : ProverKind
  ImmutableTypeChecker     : ProverKind
  CapabilityTypeChecker    : ProverKind
  BunchedTypeChecker       : ProverKind
  TemporalTypeChecker      : ProverKind
  ProvabilityTypeChecker   : ProverKind
  ImpureTypeChecker        : ProverKind
  CoeffectTypeChecker      : ProverKind
  ProbabilisticTypeChecker : ProverKind
  DyadicTypeChecker        : ProverKind
  HomotopyTypeChecker      : ProverKind
  CubicalTypeChecker       : ProverKind
  NominalTypeChecker       : ProverKind
  Abella                   : ProverKind
  Dedukti                  : ProverKind
  Cameleer                 : ProverKind
  ACL2s                    : ProverKind
  IsabelleZF               : ProverKind
  Boogie                   : ProverKind
  Naproche                 : ProverKind
  Matita                   : ProverKind
  Arend                    : ProverKind
  Athena                   : ProverKind
  LambdaProlog             : ProverKind
  Mercury                  : ProverKind
  Nitpick                  : ProverKind
  Nunchaku                 : ProverKind
  -- GPU kernel verification backends (2026-04-26)
  GPUVerify                : ProverKind
  Faial                    : ProverKind

-- ==========================================================================
-- Section 2: kind_to_u8 mapping
-- ==========================================================================

||| Maps each ProverKind to a unique Nat discriminant (0-104).
||| This mirrors the implicit Rust enum discriminant ordering.
public export
kindToU8 : ProverKind -> Nat
kindToU8 Agda                     = 0
kindToU8 Coq                      = 1
kindToU8 Lean                     = 2
kindToU8 Isabelle                 = 3
kindToU8 Z3                       = 4
kindToU8 CVC5                     = 5
kindToU8 Metamath                 = 6
kindToU8 HOLLight                 = 7
kindToU8 Mizar                    = 8
kindToU8 PVS                      = 9
kindToU8 ACL2                     = 10
kindToU8 HOL4                     = 11
kindToU8 Idris2                   = 12
kindToU8 Lean3                    = 13
kindToU8 Vampire                  = 14
kindToU8 EProver                  = 15
kindToU8 SPASS                    = 16
kindToU8 AltErgo                  = 17
kindToU8 FStar                    = 18
kindToU8 Dafny                    = 19
kindToU8 Why3                     = 20
kindToU8 TLAPS                    = 21
kindToU8 Twelf                    = 22
kindToU8 Nuprl                    = 23
kindToU8 Minlog                   = 24
kindToU8 Imandra                  = 25
kindToU8 GLPK                     = 26
kindToU8 SCIP                     = 27
kindToU8 MiniZinc                 = 28
kindToU8 Chuffed                  = 29
kindToU8 ORTools                  = 30
kindToU8 TypedWasm                = 31
kindToU8 SPIN                     = 32
kindToU8 CBMC                     = 33
kindToU8 SeaHorn                  = 34
kindToU8 CaDiCaL                  = 35
kindToU8 Kissat                   = 36
kindToU8 MiniSat                  = 37
kindToU8 NuSMV                    = 38
kindToU8 TLC                      = 39
kindToU8 Alloy                    = 40
kindToU8 Prism                    = 41
kindToU8 UPPAAL                   = 42
kindToU8 FramaC                   = 43
kindToU8 Viper                    = 44
kindToU8 Tamarin                  = 45
kindToU8 ProVerif                 = 46
kindToU8 KeY                      = 47
kindToU8 DReal                    = 48
kindToU8 ABC                      = 49
kindToU8 TypeLL                   = 50
kindToU8 KatagoriaVerifier        = 51
kindToU8 TropicalTypeChecker      = 52
kindToU8 ChoreographicTypeChecker = 53
kindToU8 EpistemicTypeChecker     = 54
kindToU8 EchoTypeChecker          = 55
kindToU8 SessionTypeChecker       = 56
kindToU8 ModalTypeChecker         = 57
kindToU8 QTTTypeChecker           = 58
kindToU8 EffectRowTypeChecker     = 59
kindToU8 DependentTypeChecker     = 60
kindToU8 RefinementTypeChecker    = 61
kindToU8 OrdinaryTypeChecker      = 62
kindToU8 PhantomTypeChecker       = 63
kindToU8 PolymorphicTypeChecker   = 64
kindToU8 ExistentialTypeChecker   = 65
kindToU8 HigherKindedTypeChecker  = 66
kindToU8 RowTypeChecker           = 67
kindToU8 SubtypingTypeChecker     = 68
kindToU8 IntersectionTypeChecker  = 69
kindToU8 UnionTypeChecker         = 70
kindToU8 GradualTypeChecker       = 71
kindToU8 HoareTypeChecker         = 72
kindToU8 IndexedTypeChecker       = 73
kindToU8 LinearTypeChecker        = 74
kindToU8 AffineTypeChecker        = 75
kindToU8 RelevantTypeChecker      = 76
kindToU8 OrderedTypeChecker       = 77
kindToU8 UniquenessTypeChecker    = 78
kindToU8 ImmutableTypeChecker     = 79
kindToU8 CapabilityTypeChecker    = 80
kindToU8 BunchedTypeChecker       = 81
kindToU8 TemporalTypeChecker      = 82
kindToU8 ProvabilityTypeChecker   = 83
kindToU8 ImpureTypeChecker        = 84
kindToU8 CoeffectTypeChecker      = 85
kindToU8 ProbabilisticTypeChecker = 86
kindToU8 DyadicTypeChecker        = 87
kindToU8 HomotopyTypeChecker      = 88
kindToU8 CubicalTypeChecker       = 89
kindToU8 NominalTypeChecker       = 90
kindToU8 Abella                   = 91
kindToU8 Dedukti                  = 92
kindToU8 Cameleer                 = 93
kindToU8 ACL2s                    = 94
kindToU8 IsabelleZF               = 95
kindToU8 Boogie                   = 96
kindToU8 Naproche                 = 97
kindToU8 Matita                   = 98
kindToU8 Arend                    = 99
kindToU8 Athena                   = 100
kindToU8 LambdaProlog             = 101
kindToU8 Mercury                  = 102
kindToU8 Nitpick                  = 103
kindToU8 Nunchaku                 = 104
kindToU8 GPUVerify                = 105
kindToU8 Faial                    = 106

-- ==========================================================================
-- Section 3: Inverse mapping (u8 -> ProverKind)
-- ==========================================================================

||| Inverse of kindToU8.  Returns Nothing for values outside [0, 104].
public export
u8ToKind : Nat -> Maybe ProverKind
u8ToKind 0   = Just Agda
u8ToKind 1   = Just Coq
u8ToKind 2   = Just Lean
u8ToKind 3   = Just Isabelle
u8ToKind 4   = Just Z3
u8ToKind 5   = Just CVC5
u8ToKind 6   = Just Metamath
u8ToKind 7   = Just HOLLight
u8ToKind 8   = Just Mizar
u8ToKind 9   = Just PVS
u8ToKind 10  = Just ACL2
u8ToKind 11  = Just HOL4
u8ToKind 12  = Just Idris2
u8ToKind 13  = Just Lean3
u8ToKind 14  = Just Vampire
u8ToKind 15  = Just EProver
u8ToKind 16  = Just SPASS
u8ToKind 17  = Just AltErgo
u8ToKind 18  = Just FStar
u8ToKind 19  = Just Dafny
u8ToKind 20  = Just Why3
u8ToKind 21  = Just TLAPS
u8ToKind 22  = Just Twelf
u8ToKind 23  = Just Nuprl
u8ToKind 24  = Just Minlog
u8ToKind 25  = Just Imandra
u8ToKind 26  = Just GLPK
u8ToKind 27  = Just SCIP
u8ToKind 28  = Just MiniZinc
u8ToKind 29  = Just Chuffed
u8ToKind 30  = Just ORTools
u8ToKind 31  = Just TypedWasm
u8ToKind 32  = Just SPIN
u8ToKind 33  = Just CBMC
u8ToKind 34  = Just SeaHorn
u8ToKind 35  = Just CaDiCaL
u8ToKind 36  = Just Kissat
u8ToKind 37  = Just MiniSat
u8ToKind 38  = Just NuSMV
u8ToKind 39  = Just TLC
u8ToKind 40  = Just Alloy
u8ToKind 41  = Just Prism
u8ToKind 42  = Just UPPAAL
u8ToKind 43  = Just FramaC
u8ToKind 44  = Just Viper
u8ToKind 45  = Just Tamarin
u8ToKind 46  = Just ProVerif
u8ToKind 47  = Just KeY
u8ToKind 48  = Just DReal
u8ToKind 49  = Just ABC
u8ToKind 50  = Just TypeLL
u8ToKind 51  = Just KatagoriaVerifier
u8ToKind 52  = Just TropicalTypeChecker
u8ToKind 53  = Just ChoreographicTypeChecker
u8ToKind 54  = Just EpistemicTypeChecker
u8ToKind 55  = Just EchoTypeChecker
u8ToKind 56  = Just SessionTypeChecker
u8ToKind 57  = Just ModalTypeChecker
u8ToKind 58  = Just QTTTypeChecker
u8ToKind 59  = Just EffectRowTypeChecker
u8ToKind 60  = Just DependentTypeChecker
u8ToKind 61  = Just RefinementTypeChecker
u8ToKind 62  = Just OrdinaryTypeChecker
u8ToKind 63  = Just PhantomTypeChecker
u8ToKind 64  = Just PolymorphicTypeChecker
u8ToKind 65  = Just ExistentialTypeChecker
u8ToKind 66  = Just HigherKindedTypeChecker
u8ToKind 67  = Just RowTypeChecker
u8ToKind 68  = Just SubtypingTypeChecker
u8ToKind 69  = Just IntersectionTypeChecker
u8ToKind 70  = Just UnionTypeChecker
u8ToKind 71  = Just GradualTypeChecker
u8ToKind 72  = Just HoareTypeChecker
u8ToKind 73  = Just IndexedTypeChecker
u8ToKind 74  = Just LinearTypeChecker
u8ToKind 75  = Just AffineTypeChecker
u8ToKind 76  = Just RelevantTypeChecker
u8ToKind 77  = Just OrderedTypeChecker
u8ToKind 78  = Just UniquenessTypeChecker
u8ToKind 79  = Just ImmutableTypeChecker
u8ToKind 80  = Just CapabilityTypeChecker
u8ToKind 81  = Just BunchedTypeChecker
u8ToKind 82  = Just TemporalTypeChecker
u8ToKind 83  = Just ProvabilityTypeChecker
u8ToKind 84  = Just ImpureTypeChecker
u8ToKind 85  = Just CoeffectTypeChecker
u8ToKind 86  = Just ProbabilisticTypeChecker
u8ToKind 87  = Just DyadicTypeChecker
u8ToKind 88  = Just HomotopyTypeChecker
u8ToKind 89  = Just CubicalTypeChecker
u8ToKind 90  = Just NominalTypeChecker
u8ToKind 91  = Just Abella
u8ToKind 92  = Just Dedukti
u8ToKind 93  = Just Cameleer
u8ToKind 94  = Just ACL2s
u8ToKind 95  = Just IsabelleZF
u8ToKind 96  = Just Boogie
u8ToKind 97  = Just Naproche
u8ToKind 98  = Just Matita
u8ToKind 99  = Just Arend
u8ToKind 100 = Just Athena
u8ToKind 101 = Just LambdaProlog
u8ToKind 102 = Just Mercury
u8ToKind 103 = Just Nitpick
u8ToKind 104 = Just Nunchaku
u8ToKind 105 = Just GPUVerify
u8ToKind 106 = Just Faial
u8ToKind _   = Nothing

-- ==========================================================================
-- Section 4: Round-trip proof (u8ToKind . kindToU8 = Just)
-- ==========================================================================

||| Round-trip: u8ToKind (kindToU8 k) = Just k for all k.
public export
roundTrip : (k : ProverKind) -> u8ToKind (kindToU8 k) = Just k
roundTrip Agda                     = Refl
roundTrip Coq                      = Refl
roundTrip Lean                     = Refl
roundTrip Isabelle                 = Refl
roundTrip Z3                       = Refl
roundTrip CVC5                     = Refl
roundTrip Metamath                 = Refl
roundTrip HOLLight                 = Refl
roundTrip Mizar                    = Refl
roundTrip PVS                      = Refl
roundTrip ACL2                     = Refl
roundTrip HOL4                     = Refl
roundTrip Idris2                   = Refl
roundTrip Lean3                    = Refl
roundTrip Vampire                  = Refl
roundTrip EProver                  = Refl
roundTrip SPASS                    = Refl
roundTrip AltErgo                  = Refl
roundTrip FStar                    = Refl
roundTrip Dafny                    = Refl
roundTrip Why3                     = Refl
roundTrip TLAPS                    = Refl
roundTrip Twelf                    = Refl
roundTrip Nuprl                    = Refl
roundTrip Minlog                   = Refl
roundTrip Imandra                  = Refl
roundTrip GLPK                     = Refl
roundTrip SCIP                     = Refl
roundTrip MiniZinc                 = Refl
roundTrip Chuffed                  = Refl
roundTrip ORTools                  = Refl
roundTrip TypedWasm                = Refl
roundTrip SPIN                     = Refl
roundTrip CBMC                     = Refl
roundTrip SeaHorn                  = Refl
roundTrip CaDiCaL                  = Refl
roundTrip Kissat                   = Refl
roundTrip MiniSat                  = Refl
roundTrip NuSMV                    = Refl
roundTrip TLC                      = Refl
roundTrip Alloy                    = Refl
roundTrip Prism                    = Refl
roundTrip UPPAAL                   = Refl
roundTrip FramaC                   = Refl
roundTrip Viper                    = Refl
roundTrip Tamarin                  = Refl
roundTrip ProVerif                 = Refl
roundTrip KeY                      = Refl
roundTrip DReal                    = Refl
roundTrip ABC                      = Refl
roundTrip TypeLL                   = Refl
roundTrip KatagoriaVerifier        = Refl
roundTrip TropicalTypeChecker      = Refl
roundTrip ChoreographicTypeChecker = Refl
roundTrip EpistemicTypeChecker     = Refl
roundTrip EchoTypeChecker          = Refl
roundTrip SessionTypeChecker       = Refl
roundTrip ModalTypeChecker         = Refl
roundTrip QTTTypeChecker           = Refl
roundTrip EffectRowTypeChecker     = Refl
roundTrip DependentTypeChecker     = Refl
roundTrip RefinementTypeChecker    = Refl
roundTrip OrdinaryTypeChecker      = Refl
roundTrip PhantomTypeChecker       = Refl
roundTrip PolymorphicTypeChecker   = Refl
roundTrip ExistentialTypeChecker   = Refl
roundTrip HigherKindedTypeChecker  = Refl
roundTrip RowTypeChecker           = Refl
roundTrip SubtypingTypeChecker     = Refl
roundTrip IntersectionTypeChecker  = Refl
roundTrip UnionTypeChecker         = Refl
roundTrip GradualTypeChecker       = Refl
roundTrip HoareTypeChecker         = Refl
roundTrip IndexedTypeChecker       = Refl
roundTrip LinearTypeChecker        = Refl
roundTrip AffineTypeChecker        = Refl
roundTrip RelevantTypeChecker      = Refl
roundTrip OrderedTypeChecker       = Refl
roundTrip UniquenessTypeChecker    = Refl
roundTrip ImmutableTypeChecker     = Refl
roundTrip CapabilityTypeChecker    = Refl
roundTrip BunchedTypeChecker       = Refl
roundTrip TemporalTypeChecker      = Refl
roundTrip ProvabilityTypeChecker   = Refl
roundTrip ImpureTypeChecker        = Refl
roundTrip CoeffectTypeChecker      = Refl
roundTrip ProbabilisticTypeChecker = Refl
roundTrip DyadicTypeChecker        = Refl
roundTrip HomotopyTypeChecker      = Refl
roundTrip CubicalTypeChecker       = Refl
roundTrip NominalTypeChecker       = Refl
roundTrip Abella                   = Refl
roundTrip Dedukti                  = Refl
roundTrip Cameleer                 = Refl
roundTrip ACL2s                    = Refl
roundTrip IsabelleZF               = Refl
roundTrip Boogie                   = Refl
roundTrip Naproche                 = Refl
roundTrip Matita                   = Refl
roundTrip Arend                    = Refl
roundTrip Athena                   = Refl
roundTrip LambdaProlog             = Refl
roundTrip Mercury                  = Refl
roundTrip Nitpick                  = Refl
roundTrip Nunchaku                 = Refl
roundTrip GPUVerify                = Refl
roundTrip Faial                    = Refl

-- ==========================================================================
-- Section 5: Injectivity proof (kindToU8 a = kindToU8 b -> a = b)
-- ==========================================================================

public export
kindToU8Injective : (a, b : ProverKind) -> kindToU8 a = kindToU8 b -> a = b
kindToU8Injective a b prf =
  let leftRoundTrip  = roundTrip a
      rightRoundTrip = roundTrip b
      step1 = replace {p = \x => u8ToKind x = Just a} prf leftRoundTrip
      justEq = trans (sym step1) rightRoundTrip
  in justInjective justEq
  where
    justInjective : {0 x, y : t} -> Just x = Just y -> x = y
    justInjective Refl = Refl

-- ==========================================================================
-- Section 6: Variant count witness
-- ==========================================================================

public export
proverKindCount : Nat
proverKindCount = 107

public export
maxDiscriminant : Nat
maxDiscriminant = 106

||| Every discriminant is within the valid range [0, 104].
public export
discriminantBounded : (k : ProverKind) -> LTE (kindToU8 k) 106
discriminantBounded Agda                     = LTEZero
discriminantBounded Coq                      = LTESucc (LTEZero)
discriminantBounded Lean                     = LTESucc (LTESucc (LTEZero))
discriminantBounded Isabelle                 = LTESucc (LTESucc (LTESucc (LTEZero)))
discriminantBounded Z3                       = LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))
discriminantBounded CVC5                     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))
discriminantBounded Metamath                 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))
discriminantBounded HOLLight                 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))
discriminantBounded Mizar                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))
discriminantBounded PVS                      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))
discriminantBounded ACL2                     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))
discriminantBounded HOL4                     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))
discriminantBounded Idris2                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))
discriminantBounded Lean3                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))
discriminantBounded Vampire                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))
discriminantBounded EProver                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))
discriminantBounded SPASS                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))
discriminantBounded AltErgo                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))
discriminantBounded FStar                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))
discriminantBounded Dafny                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))
discriminantBounded Why3                     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))
discriminantBounded TLAPS                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))
discriminantBounded Twelf                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))
discriminantBounded Nuprl                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))
discriminantBounded Minlog                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))
discriminantBounded Imandra                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))
discriminantBounded GLPK                     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))
discriminantBounded SCIP                     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))
discriminantBounded MiniZinc                 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))
discriminantBounded Chuffed                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))
discriminantBounded ORTools                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))
discriminantBounded TypedWasm                = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))
discriminantBounded SPIN                     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))
discriminantBounded CBMC                     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))
discriminantBounded SeaHorn                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))
discriminantBounded CaDiCaL                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))
discriminantBounded Kissat                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))
discriminantBounded MiniSat                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))
discriminantBounded NuSMV                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))
discriminantBounded TLC                      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))
discriminantBounded Alloy                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))
discriminantBounded Prism                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))
discriminantBounded UPPAAL                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))
discriminantBounded FramaC                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Viper                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Tamarin                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ProVerif                 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded KeY                      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded DReal                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ABC                      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded TypeLL                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded KatagoriaVerifier        = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded TropicalTypeChecker      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ChoreographicTypeChecker = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded EpistemicTypeChecker     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded EchoTypeChecker          = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded SessionTypeChecker       = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ModalTypeChecker         = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded QTTTypeChecker           = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded EffectRowTypeChecker     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded DependentTypeChecker     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded RefinementTypeChecker    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded OrdinaryTypeChecker      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded PhantomTypeChecker       = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded PolymorphicTypeChecker   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ExistentialTypeChecker   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded HigherKindedTypeChecker  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded RowTypeChecker           = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded SubtypingTypeChecker     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded IntersectionTypeChecker  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded UnionTypeChecker         = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded GradualTypeChecker       = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded HoareTypeChecker         = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded IndexedTypeChecker       = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded LinearTypeChecker        = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded AffineTypeChecker        = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded RelevantTypeChecker      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded OrderedTypeChecker       = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded UniquenessTypeChecker    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ImmutableTypeChecker     = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded CapabilityTypeChecker    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded BunchedTypeChecker       = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded TemporalTypeChecker      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ProvabilityTypeChecker   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ImpureTypeChecker        = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded CoeffectTypeChecker      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ProbabilisticTypeChecker = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded DyadicTypeChecker        = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded HomotopyTypeChecker      = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded CubicalTypeChecker       = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded NominalTypeChecker       = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Abella                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Dedukti                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Cameleer                 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded ACL2s                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded IsabelleZF               = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Boogie                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Naproche                 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Matita                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Arend                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Athena                   = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded LambdaProlog             = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Mercury                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Nitpick                  = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Nunchaku                 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded GPUVerify                = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
discriminantBounded Faial                    = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTEZero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
