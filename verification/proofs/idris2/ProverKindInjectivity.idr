-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ProverKindInjectivity.idr
--
-- Proves that the kind_to_u8 mapping from ProverKind to Nat is injective:
-- no two distinct prover variants share the same numeric discriminant.
-- This guarantees collision-free serialisation and dispatch.
--
-- Models all 49 ProverKind variants from src/rust/provers/mod.rs.
--
-- Uses %default total to enforce totality on every definition.

module ProverKindInjectivity

%default total

-- ==========================================================================
-- Section 1: ProverKind -- all 49 variants
-- ==========================================================================

||| All 49 prover backends supported by Echidna, mirroring
||| the ProverKind enum in src/rust/provers/mod.rs.
public export
data ProverKind : Type where
  -- Tier 1: Original + SMT solvers
  Agda      : ProverKind
  Coq       : ProverKind
  Lean      : ProverKind
  Isabelle  : ProverKind
  Z3        : ProverKind
  CVC5      : ProverKind
  -- Tier 2: "Big Six" completion
  Metamath  : ProverKind
  HOLLight  : ProverKind
  Mizar     : ProverKind
  -- Tier 3: Additional coverage
  PVS       : ProverKind
  ACL2      : ProverKind
  -- Tier 4: Advanced
  HOL4      : ProverKind
  -- Extended
  Idris2    : ProverKind
  -- Tier 5: First-Order ATPs
  Vampire   : ProverKind
  EProver   : ProverKind
  SPASS     : ProverKind
  AltErgo   : ProverKind
  -- Tier 6: Dependent types + effects, auto-active
  FStar     : ProverKind
  Dafny     : ProverKind
  Why3      : ProverKind
  -- Tier 7: Specialized / niche
  TLAPS     : ProverKind
  Twelf     : ProverKind
  Nuprl     : ProverKind
  Minlog    : ProverKind
  Imandra   : ProverKind
  -- Tier 8: Constraint solvers
  GLPK      : ProverKind
  SCIP      : ProverKind
  MiniZinc  : ProverKind
  Chuffed   : ProverKind
  ORTools   : ProverKind
  -- Prover oracles
  TypedWasm : ProverKind
  -- Tier 9: Model checkers and program verifiers
  SPIN      : ProverKind
  CBMC      : ProverKind
  SeaHorn   : ProverKind
  -- Tier 9: SAT Solvers
  CaDiCaL   : ProverKind
  Kissat    : ProverKind
  MiniSat   : ProverKind
  -- Tier 9: Model checkers (extended)
  NuSMV     : ProverKind
  TLC       : ProverKind
  Alloy     : ProverKind
  Prism     : ProverKind
  UPPAAL    : ProverKind
  -- Tier 9: Program verifiers (deductive)
  FramaC    : ProverKind
  -- Tier 9: Permission-based
  Viper     : ProverKind
  -- Tier 9: Security protocol verifiers
  Tamarin   : ProverKind
  ProVerif  : ProverKind
  -- Tier 9: Deductive Java verifiers
  KeY       : ProverKind
  -- Tier 10: Delta-complete SMT solvers
  DReal     : ProverKind
  -- Tier 10: Logic synthesis & hardware verification
  ABC       : ProverKind

-- ==========================================================================
-- Section 2: kind_to_u8 mapping
-- ==========================================================================

||| Maps each ProverKind to a unique Nat discriminant (0-48).
||| This mirrors the implicit Rust enum discriminant ordering.
public export
kindToU8 : ProverKind -> Nat
kindToU8 Agda      = 0
kindToU8 Coq       = 1
kindToU8 Lean      = 2
kindToU8 Isabelle  = 3
kindToU8 Z3        = 4
kindToU8 CVC5      = 5
kindToU8 Metamath  = 6
kindToU8 HOLLight  = 7
kindToU8 Mizar     = 8
kindToU8 PVS       = 9
kindToU8 ACL2      = 10
kindToU8 HOL4      = 11
kindToU8 Idris2    = 12
kindToU8 Vampire   = 13
kindToU8 EProver   = 14
kindToU8 SPASS     = 15
kindToU8 AltErgo   = 16
kindToU8 FStar     = 17
kindToU8 Dafny     = 18
kindToU8 Why3      = 19
kindToU8 TLAPS     = 20
kindToU8 Twelf     = 21
kindToU8 Nuprl     = 22
kindToU8 Minlog    = 23
kindToU8 Imandra   = 24
kindToU8 GLPK      = 25
kindToU8 SCIP      = 26
kindToU8 MiniZinc  = 27
kindToU8 Chuffed   = 28
kindToU8 ORTools   = 29
kindToU8 TypedWasm = 30
kindToU8 SPIN      = 31
kindToU8 CBMC      = 32
kindToU8 SeaHorn   = 33
kindToU8 CaDiCaL   = 34
kindToU8 Kissat    = 35
kindToU8 MiniSat   = 36
kindToU8 NuSMV     = 37
kindToU8 TLC       = 38
kindToU8 Alloy     = 39
kindToU8 Prism     = 40
kindToU8 UPPAAL    = 41
kindToU8 FramaC    = 42
kindToU8 Viper     = 43
kindToU8 Tamarin   = 44
kindToU8 ProVerif  = 45
kindToU8 KeY       = 46
kindToU8 DReal     = 47
kindToU8 ABC       = 48

-- ==========================================================================
-- Section 3: Inverse mapping (u8 -> ProverKind)
-- ==========================================================================

||| Inverse of kindToU8.  Returns Nothing for values outside [0, 48].
public export
u8ToKind : Nat -> Maybe ProverKind
u8ToKind 0  = Just Agda
u8ToKind 1  = Just Coq
u8ToKind 2  = Just Lean
u8ToKind 3  = Just Isabelle
u8ToKind 4  = Just Z3
u8ToKind 5  = Just CVC5
u8ToKind 6  = Just Metamath
u8ToKind 7  = Just HOLLight
u8ToKind 8  = Just Mizar
u8ToKind 9  = Just PVS
u8ToKind 10 = Just ACL2
u8ToKind 11 = Just HOL4
u8ToKind 12 = Just Idris2
u8ToKind 13 = Just Vampire
u8ToKind 14 = Just EProver
u8ToKind 15 = Just SPASS
u8ToKind 16 = Just AltErgo
u8ToKind 17 = Just FStar
u8ToKind 18 = Just Dafny
u8ToKind 19 = Just Why3
u8ToKind 20 = Just TLAPS
u8ToKind 21 = Just Twelf
u8ToKind 22 = Just Nuprl
u8ToKind 23 = Just Minlog
u8ToKind 24 = Just Imandra
u8ToKind 25 = Just GLPK
u8ToKind 26 = Just SCIP
u8ToKind 27 = Just MiniZinc
u8ToKind 28 = Just Chuffed
u8ToKind 29 = Just ORTools
u8ToKind 30 = Just TypedWasm
u8ToKind 31 = Just SPIN
u8ToKind 32 = Just CBMC
u8ToKind 33 = Just SeaHorn
u8ToKind 34 = Just CaDiCaL
u8ToKind 35 = Just Kissat
u8ToKind 36 = Just MiniSat
u8ToKind 37 = Just NuSMV
u8ToKind 38 = Just TLC
u8ToKind 39 = Just Alloy
u8ToKind 40 = Just Prism
u8ToKind 41 = Just UPPAAL
u8ToKind 42 = Just FramaC
u8ToKind 43 = Just Viper
u8ToKind 44 = Just Tamarin
u8ToKind 45 = Just ProVerif
u8ToKind 46 = Just KeY
u8ToKind 47 = Just DReal
u8ToKind 48 = Just ABC
u8ToKind _  = Nothing

-- ==========================================================================
-- Section 4: Round-trip proof (u8ToKind . kindToU8 = Just)
-- ==========================================================================

||| Round-trip: u8ToKind (kindToU8 k) = Just k for all k.
||| This is a stronger property than injectivity -- it proves that
||| the mapping is a proper left inverse.
public export
roundTrip : (k : ProverKind) -> u8ToKind (kindToU8 k) = Just k
roundTrip Agda      = Refl
roundTrip Coq       = Refl
roundTrip Lean      = Refl
roundTrip Isabelle  = Refl
roundTrip Z3        = Refl
roundTrip CVC5      = Refl
roundTrip Metamath  = Refl
roundTrip HOLLight  = Refl
roundTrip Mizar     = Refl
roundTrip PVS       = Refl
roundTrip ACL2      = Refl
roundTrip HOL4      = Refl
roundTrip Idris2    = Refl
roundTrip Vampire   = Refl
roundTrip EProver   = Refl
roundTrip SPASS     = Refl
roundTrip AltErgo   = Refl
roundTrip FStar     = Refl
roundTrip Dafny     = Refl
roundTrip Why3      = Refl
roundTrip TLAPS     = Refl
roundTrip Twelf     = Refl
roundTrip Nuprl     = Refl
roundTrip Minlog    = Refl
roundTrip Imandra   = Refl
roundTrip GLPK      = Refl
roundTrip SCIP      = Refl
roundTrip MiniZinc  = Refl
roundTrip Chuffed   = Refl
roundTrip ORTools   = Refl
roundTrip TypedWasm = Refl
roundTrip SPIN      = Refl
roundTrip CBMC      = Refl
roundTrip SeaHorn   = Refl
roundTrip CaDiCaL   = Refl
roundTrip Kissat    = Refl
roundTrip MiniSat   = Refl
roundTrip NuSMV     = Refl
roundTrip TLC       = Refl
roundTrip Alloy     = Refl
roundTrip Prism     = Refl
roundTrip UPPAAL    = Refl
roundTrip FramaC    = Refl
roundTrip Viper     = Refl
roundTrip Tamarin   = Refl
roundTrip ProVerif  = Refl
roundTrip KeY       = Refl
roundTrip DReal     = Refl
roundTrip ABC       = Refl

-- ==========================================================================
-- Section 5: Injectivity proof (kindToU8 a = kindToU8 b -> a = b)
-- ==========================================================================

||| CORE THEOREM: kindToU8 is injective.
||| If two ProverKind values map to the same Nat, they are equal.
|||
||| Proof strategy: we use the round-trip property.
||| Given kindToU8 a = kindToU8 b, apply u8ToKind to both sides.
||| By roundTrip, u8ToKind (kindToU8 a) = Just a and
||| u8ToKind (kindToU8 b) = Just b.  Since kindToU8 a = kindToU8 b,
||| we get Just a = Just b, hence a = b.
public export
kindToU8Injective : (a, b : ProverKind) -> kindToU8 a = kindToU8 b -> a = b
kindToU8Injective a b prf =
  let leftRoundTrip  = roundTrip a  -- : u8ToKind (kindToU8 a) = Just a
      rightRoundTrip = roundTrip b  -- : u8ToKind (kindToU8 b) = Just b
      -- rewrite kindToU8 a with kindToU8 b in leftRoundTrip
      step1 = replace {p = \x => u8ToKind x = Just a} prf leftRoundTrip
      -- now: u8ToKind (kindToU8 b) = Just a
      -- and: u8ToKind (kindToU8 b) = Just b
      -- therefore: Just a = Just b
      justEq = trans (sym step1) rightRoundTrip
  in justInjective justEq
  where
    ||| Just is injective: Just a = Just b -> a = b
    justInjective : {0 x, y : t} -> Just x = Just y -> x = y
    justInjective Refl = Refl

-- ==========================================================================
-- Section 6: Variant count witness
-- ==========================================================================

||| Total number of ProverKind variants.
||| Compile-time witness that matches the Rust enum.
public export
proverKindCount : Nat
proverKindCount = 49

||| The discriminant range is [0, 48], which is exactly proverKindCount - 1.
public export
maxDiscriminant : Nat
maxDiscriminant = 48

-- Helper: build LTE n 48 from a strict predecessor proof.
-- Note: LTEZero : LTE 0 n, and LTESucc : LTE n m -> LTE (S n) (S m).
-- So LTE k 48 is built by k nested LTESucc around LTEZero, giving LTE k k,
-- then 48-k applications of lteSuccRight lift it to LTE k 48.

||| Every discriminant is within the valid range [0, 48].
||| Proven by case analysis: each variant's discriminant is computed
||| directly. Uses lteSuccRight repeatedly to lift LTE k k into LTE k 48.
public export
discriminantBounded : (k : ProverKind) -> LTE (kindToU8 k) maxDiscriminant
discriminantBounded Agda      = LTEZero
discriminantBounded Coq       = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Lean      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Isabelle  = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Z3        = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded CVC5      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Metamath  = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded HOLLight  = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Mizar     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded PVS       = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded ACL2      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded HOL4      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Idris2    = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Vampire   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded EProver   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded SPASS     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded AltErgo   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded FStar     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Dafny     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Why3      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded TLAPS     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Twelf     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Nuprl     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Minlog    = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Imandra   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded GLPK      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded SCIP      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded MiniZinc  = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Chuffed   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded ORTools   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded TypedWasm = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded SPIN      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded CBMC      = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded SeaHorn   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded CaDiCaL   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Kissat    = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded MiniSat   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded NuSMV     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded TLC       = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Alloy     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Prism     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded UPPAAL    = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded FramaC    = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Viper     = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded Tamarin   = lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded ProVerif  = lteSuccRight $ lteSuccRight $ lteSuccRight LTERefl
discriminantBounded KeY       = lteSuccRight $ lteSuccRight LTERefl
discriminantBounded DReal     = lteSuccRight LTERefl
discriminantBounded ABC       = LTERefl
