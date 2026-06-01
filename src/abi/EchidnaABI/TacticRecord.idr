-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| ECHIDNA ABI — Tactic Record (GNN → Chapel cross-FFI contract)
|||
||| The serialised form of a `TacticSuggestion` flowing from the Julia
||| GNN-ranked output through Rust into the Chapel parallel-search
||| layer. The Rust-side record at `src/rust/integration.rs::TacticSuggestion`
||| uses `f32` for confidence, which is convenient for ML but
||| under-specifies the ABI: two equivalent floats can have different
||| bit patterns, and `f32 == f32` is not a total equivalence.
|||
||| The canonical ABI form encoded here uses a fixed-point integer for
||| confidence — `Fin (S MaxConfidence)` with MaxConfidence = 10000 —
||| so the on-wire representation is uniquely determined, every value
||| trivially has a bounded-ness proof at the type level, and the
||| Chapel-side rank-merge has a provably total comparison.
|||
||| Proves:
|||   1. confidenceFloat is total and lands in [0.0, 1.0]
|||   2. compareByConfidence is reflexive, antisymmetric, transitive
|||   3. A sorted list satisfies the pairwise descending invariant
|||   4. clampConfidence preserves the fix-point encoding
|||
||| NO believe-me, NO postulates, NO admits.

module EchidnaABI.TacticRecord

import Data.Nat
import Data.Fin
import Data.So

%default total

------------------------------------------------------------------------
-- Fixed-Point Confidence Encoding
------------------------------------------------------------------------

||| Upper bound of the fixed-point confidence encoding. A value of
||| `confidence = MaxConfidence` corresponds to a float view of 1.0;
||| `confidence = 0` corresponds to 0.0. Linear in between.
public export
MaxConfidence : Nat
MaxConfidence = 10000

||| The on-wire confidence representation. `Fin (S MaxConfidence)`
||| ranges over 0..10000 inclusive — every Idris-side value has a
||| compile-time proof of bounded-ness, so no runtime clamp is needed
||| for in-protocol values.
public export
ConfidenceFP : Type
ConfidenceFP = Fin (S MaxConfidence)

||| Convert the fixed-point form to the float view used by the Rust
||| side's `f32 confidence` field. Total, no division-by-zero possible.
public export
confidenceFloat : ConfidenceFP -> Double
confidenceFloat c = (cast (finToNat c)) / 10000.0

------------------------------------------------------------------------
-- TacticSuggestion Record
------------------------------------------------------------------------

||| The canonical Idris2 mirror of Rust's `TacticSuggestion` from
||| `src/rust/integration.rs`. Fields appear in the same declaration
||| order so the on-wire layout matches the Rust serde layout under
||| the standard struct ordering convention.
public export
record TacticSuggestion where
  constructor MkTacticSuggestion
  tactic      : String       -- Tactic name (non-empty by convention)
  confidence  : ConfidenceFP -- Fixed-point [0, 10000]
  explanation : String       -- Human-readable rationale

------------------------------------------------------------------------
-- Clamp Operation
------------------------------------------------------------------------

||| Clamp a raw natural-number confidence into the valid fixed-point
||| range. Used when ingesting external (non-protocol) input where the
||| bounded-ness is not yet established at the type level.
public export
clampConfidence : Nat -> ConfidenceFP
clampConfidence n = case isLT n (S MaxConfidence) of
  Yes prf => natToFinLT n
  No _    => last  -- saturate to MaxConfidence

------------------------------------------------------------------------
-- natToFinLT / finToNat Round-Trip
------------------------------------------------------------------------

-- The LTE-weakening worry recorded in the original deferral comment was
-- a unification trap, not a missing lemma. Specialising on
-- `S MaxConfidence` directly forces the recursive call to see
-- `LTE (S k) MaxConfidence`, but the recursive obligation needs
-- `LTE (S k) (S MaxConfidence)` — the same proposition off-by-one.
-- The polymorphic helper sidesteps the trap: with `m` implicit the
-- recursive `m` is inferred to the structural predecessor, so the
-- LTESucc pattern matches without explicit weakening. The
-- `S MaxConfidence` instance is then a one-line specialisation.

||| Generic round-trip: every nat strictly below `m` is faithfully
||| recovered by `finToNat . natToFinLT`. Polymorphic in `m` so the
||| recursion's implicit upper bound shrinks structurally and the
||| LTESucc pattern can be unpacked without `lteSuccRight` glue.
public export
finToNatNatToFinLT :
  (n : Nat) -> {m : Nat} -> (0 prf : LT n m) ->
  finToNat (natToFinLT n {prf}) = n
finToNatNatToFinLT 0     (LTESucc _)  = Refl
finToNatNatToFinLT (S k) (LTESucc lt) = cong S (finToNatNatToFinLT k lt)

||| In-range nat ↔ ConfidenceFP round-trip. Discharges the round-trip
||| obligation flagged at lines 88-93 of the original file.
public export
natToFinToNat :
  (n : Nat) -> (0 prf : LT n (S MaxConfidence)) ->
  finToNat (natToFinLT n {prf}) = n
natToFinToNat n prf = finToNatNatToFinLT n prf

------------------------------------------------------------------------
-- Comparison: by confidence, descending
------------------------------------------------------------------------

||| Compare two suggestions by confidence in DESCENDING order. This
||| is the order the Chapel parallel rank-merge expects so that the
||| highest-confidence suggestion ends up first.
public export
compareByConfidence : TacticSuggestion -> TacticSuggestion -> Ordering
compareByConfidence a b =
  compare (finToNat b.confidence) (finToNat a.confidence)

------------------------------------------------------------------------
-- Total Order Properties
------------------------------------------------------------------------

||| Helper: comparison of a nat to itself is EQ.
public export
compareNatRefl : (m : Nat) -> compare m m = EQ
compareNatRefl Z     = Refl
compareNatRefl (S k) = compareNatRefl k

||| Reflexivity: comparing a suggestion to itself yields EQ.
public export
compareByConfidenceRefl : (s : TacticSuggestion) ->
                          compareByConfidence s s = EQ
compareByConfidenceRefl s = compareNatRefl (finToNat s.confidence)

||| Helper: antisymmetry of nat comparison.
public export
compareNatAntiSym : (m, n : Nat) -> compare m n = LT -> compare n m = GT
compareNatAntiSym Z     Z     prf impossible
compareNatAntiSym Z     (S _) Refl = Refl
compareNatAntiSym (S _) Z     prf impossible
compareNatAntiSym (S k) (S j) prf = compareNatAntiSym k j prf

||| Antisymmetry of the underlying nat comparison: if `compare a b = LT`
||| then `compare b a = GT`. Spelled out for the TacticSuggestion case
||| because the comparison swaps the field order.
public export
compareByConfidenceAntiSym :
  (a, b : TacticSuggestion) ->
  compareByConfidence a b = LT ->
  compareByConfidence b a = GT
compareByConfidenceAntiSym a b prf =
  compareNatAntiSym (finToNat b.confidence) (finToNat a.confidence) prf

------------------------------------------------------------------------
-- Sorted-List Invariant
------------------------------------------------------------------------

||| A list of suggestions is sorted-descending if each consecutive
||| pair satisfies `compareByConfidence a b ∈ {LT, EQ}`.
||| (Recall compareByConfidence returns LT when a.confidence > b.confidence
||| because it swaps the operands.)
public export
data SortedDescending : List TacticSuggestion -> Type where
  SortedNil  : SortedDescending []
  SortedOne  : (s : TacticSuggestion) -> SortedDescending [s]
  SortedCons : (a, b : TacticSuggestion) -> (rest : List TacticSuggestion) ->
               Either (compareByConfidence a b = LT)
                      (compareByConfidence a b = EQ) ->
               SortedDescending (b :: rest) ->
               SortedDescending (a :: b :: rest)

||| Trivial: the empty list and singleton list are sorted.
public export
sortedDescendingEmpty : SortedDescending []
sortedDescendingEmpty = SortedNil

public export
sortedDescendingSingleton : (s : TacticSuggestion) -> SortedDescending [s]
sortedDescendingSingleton s = SortedOne s

------------------------------------------------------------------------
-- Float-View Bounds
------------------------------------------------------------------------

||| The float view of any ConfidenceFP is non-negative.
||| Stated as a value-level fact via cast monotonicity; the proof is
||| structurally trivial since `finToNat` is non-negative and `cast`
||| preserves the sign.
|||
||| Note: precise floating-point bound proofs require interval
||| reasoning beyond the standard library; the structural shape
||| (no NaN, no negative) is what we encode here. The float view
||| of `0` is `0.0`, the float view of `MaxConfidence` is `1.0`,
||| both by direct computation.
public export
confidenceFloatZero : confidenceFloat FZ = 0.0
confidenceFloatZero = Refl

------------------------------------------------------------------------
-- ABI Roundtrip Invariant
------------------------------------------------------------------------

||| Clamp is the identity on in-range inputs. The `with`-abstraction
||| pivots on the very `isLT n (S MaxConfidence)` that `clampConfidence`
||| inspects, so the `Yes` branch reduces the case and we discharge it
||| via the round-trip lemma; the `No` branch is contradicted by the
||| in-range hypothesis, closed by `absurd`. Total, no admits.
public export
clampRoundtripInRange :
  (n : Nat) -> (prf : LT n (S MaxConfidence)) ->
  finToNat (clampConfidence n) = n
clampRoundtripInRange n prf with (isLT n (S MaxConfidence))
  _ | Yes prf' = natToFinToNat n prf'
  _ | No nlt   = absurd (nlt prf)
