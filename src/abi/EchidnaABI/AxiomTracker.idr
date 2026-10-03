-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- EchidnaABI.AxiomTracker
--
-- Idris2 ABI type specification for the axiom-policy enforcement layer.
-- This file is the *formal specification* that the SPARK implementation
-- (src/ada/spark/axiom_policy.ads/.adb) must conform to.
--
-- The key invariants stated here as dependent-type propositions are exactly
-- what GNATprove discharges on the SPARK side.  Both must agree.
--
-- NO believe-me — every proof is constructive (Refl, case analysis, or
-- explicit witnesses).

module EchidnaABI.AxiomTracker

import EchidnaABI.Types   -- ProverKind, Platform, etc.
import Data.List
import Data.List.Elem
import Data.So
import Decidable.Equality

%default total

-- ════════════════════════════════════════════════════════════════════════════
-- DangerLevel  (mirrors src/rust/verification/axiom_tracker.rs)
-- ════════════════════════════════════════════════════════════════════════════

||| The danger level assigned to an axiom usage.
||| Total order: Safe < Noted < Warning < Reject.
public export
data DangerLevel
  = Safe    -- standard library axiom; allowed unconditionally
  | Noted   -- classical axiom in constructive system; noted but allowed
  | Warning -- incomplete proof marker (sorry, Admitted); warning issued
  | Reject  -- known unsound construct; proof REJECTED

public export
Eq DangerLevel where
  Safe    == Safe    = True
  Noted   == Noted   = True
  Warning == Warning = True
  Reject  == Reject  = True
  _       == _       = False

public export
DecEq DangerLevel where
  decEq Safe    Safe    = Yes Refl
  decEq Noted   Noted   = Yes Refl
  decEq Warning Warning = Yes Refl
  decEq Reject  Reject  = Yes Refl
  decEq Safe    Noted   = No (\case Refl impossible)
  decEq Safe    Warning = No (\case Refl impossible)
  decEq Safe    Reject  = No (\case Refl impossible)
  decEq Noted   Safe    = No (\case Refl impossible)
  decEq Noted   Warning = No (\case Refl impossible)
  decEq Noted   Reject  = No (\case Refl impossible)
  decEq Warning Safe    = No (\case Refl impossible)
  decEq Warning Noted   = No (\case Refl impossible)
  decEq Warning Reject  = No (\case Refl impossible)
  decEq Reject  Safe    = No (\case Refl impossible)
  decEq Reject  Noted   = No (\case Refl impossible)
  decEq Reject  Warning = No (\case Refl impossible)

-- C-ABI wire encoding (u8 discriminant, matches Rust PartialOrd order)
public export
dangerToU8 : DangerLevel -> Bits8
dangerToU8 Safe    = 0
dangerToU8 Noted   = 1
dangerToU8 Warning = 2
dangerToU8 Reject  = 3

public export
u8ToDanger : Bits8 -> Maybe DangerLevel
u8ToDanger 0 = Just Safe
u8ToDanger 1 = Just Noted
u8ToDanger 2 = Just Warning
u8ToDanger 3 = Just Reject
u8ToDanger _ = Nothing

||| Round-trip: decode . encode = id
public export
dangerRoundTrip : (d : DangerLevel) -> u8ToDanger (dangerToU8 d) = Just d
dangerRoundTrip Safe    = Refl
dangerRoundTrip Noted   = Refl
dangerRoundTrip Warning = Refl
dangerRoundTrip Reject  = Refl

-- ════════════════════════════════════════════════════════════════════════════
-- AxiomPolicy  (mirrors Rust AxiomPolicy discriminant)
-- ════════════════════════════════════════════════════════════════════════════

||| The policy verdict for a scanned proof.
public export
data AxiomPolicy
  = PolicyClean       -- only Safe axioms; unconditionally accepted
  | PolicyClassical   -- classical axioms noted; accepted with note
  | PolicyIncomplete  -- sorry/Admitted found; accepted with warning
  | PolicyRejected    -- unsound construct; REJECTED

-- C-ABI wire encoding (i32 discriminant)
public export
policyToI32 : AxiomPolicy -> Int32
policyToI32 PolicyClean      = 0
policyToI32 PolicyClassical  = 1
policyToI32 PolicyIncomplete = 2
policyToI32 PolicyRejected   = 3

||| A proof is acceptable if and only if the policy is not PolicyRejected.
public export
isAcceptable : AxiomPolicy -> Bool
isAcceptable PolicyRejected = False
isAcceptable _              = True

-- ════════════════════════════════════════════════════════════════════════════
-- The two central soundness invariants
-- (These are what SPARK GNATprove formally verifies on the Ada side.)
-- ════════════════════════════════════════════════════════════════════════════

||| Structural existential over a danger level.  Unlike the Foldable `any`
||| (which folds via `foldl`, so it does NOT reduce on cons), this recurses
||| structurally — letting the soundness/precision proofs below go through by
||| induction with definitional reduction of the head test `x == d`.
public export
hasDanger : DangerLevel -> List DangerLevel -> Bool
hasDanger _ []        = False
hasDanger d (x :: xs) = (x == d) || hasDanger d xs

||| Specification of enforcePolicySpec: the reference function that the
||| SPARK implementation must replicate.
|||
||| This is NOT the live callable; it is the specification the bridge tests
||| against via cross-check mode.
public export
enforcePolicySpec : List DangerLevel -> AxiomPolicy
enforcePolicySpec usages =
  if hasDanger Reject usages then PolicyRejected
  else if hasDanger Warning usages then PolicyIncomplete
  else if hasDanger Noted usages then PolicyClassical
  else PolicyClean

-- ────────────────────────────────────────────────────────────────────────────
-- Invariant 1 (Soundness): Reject-in → PolicyRejected-out
-- ────────────────────────────────────────────────────────────────────────────

||| Proof that if any usage is Reject, the spec returns PolicyRejected.
public export
soundness
  : (usages : List DangerLevel)
  -> Elem Reject usages
  -> enforcePolicySpec usages = PolicyRejected
soundness usages prf =
  rewrite hasRejectIsTrue usages prf in Refl
  where
    -- Prove hasDanger Reject us = True given Reject ∈ us.
    -- Case-split on the head constructor so that 'x == Reject' reduces
    -- definitionally before applying the induction hypothesis via rewrite.
    hasRejectIsTrue
      : (us : List DangerLevel)
      -> Elem Reject us
      -> hasDanger Reject us = True
    hasRejectIsTrue []              p          = absurd p
    hasRejectIsTrue (Reject  :: _)  Here       = Refl
    hasRejectIsTrue (Safe    :: xs) (There p)  = rewrite hasRejectIsTrue xs p in Refl
    hasRejectIsTrue (Noted   :: xs) (There p)  = rewrite hasRejectIsTrue xs p in Refl
    hasRejectIsTrue (Warning :: xs) (There p)  = rewrite hasRejectIsTrue xs p in Refl
    hasRejectIsTrue (Reject  :: xs) (There _)  = Refl

-- ────────────────────────────────────────────────────────────────────────────
-- Invariant 2 (Precision): no Reject-in → not PolicyRejected-out
-- ────────────────────────────────────────────────────────────────────────────

||| Proof that if no usage is Reject, the spec never returns PolicyRejected.
public export
precision
  : (usages : List DangerLevel)
  -> ((e : DangerLevel) -> Elem e usages -> Not (e = Reject))
  -> Not (enforcePolicySpec usages = PolicyRejected)
precision usages noReject prf =
  -- A PolicyRejected verdict forces the Reject flag True (rejTrue); the
  -- no-Reject hypothesis forces it False — contradiction.
  absurd (trans (sym (rejTrue usages prf)) (noRejectMeansFalse usages noReject))
  where
    -- enforcePolicySpec us = PolicyRejected can only arise via the Reject
    -- guard.  `with` on each flag lets the spec reduce per branch, so every
    -- non-Reject branch contradicts `p` and the Reject branch returns Refl.
    rejTrue : (us : List DangerLevel) ->
              enforcePolicySpec us = PolicyRejected -> hasDanger Reject us = True
    rejTrue us p with (hasDanger Reject us)
      rejTrue us p | True = Refl
      rejTrue us p | False with (hasDanger Warning us)
        rejTrue us p | False | True = case p of { Refl impossible }
        rejTrue us p | False | False with (hasDanger Noted us)
          rejTrue us p | False | False | True  = case p of { Refl impossible }
          rejTrue us p | False | False | False = case p of { Refl impossible }

    -- No Reject in the list ⇒ the structural Reject check is False.
    -- 'x == Reject' reduces definitionally, so 'False || hasDanger Reject xs'
    -- collapses to the inductive hypothesis.
    noRejectMeansFalse
      : (us : List DangerLevel)
      -> ((e : DangerLevel) -> Elem e us -> Not (e = Reject))
      -> hasDanger Reject us = False
    noRejectMeansFalse [] _ = Refl
    noRejectMeansFalse (Safe    :: xs) noR =
      rewrite noRejectMeansFalse xs (\e, p => noR e (There p)) in Refl
    noRejectMeansFalse (Noted   :: xs) noR =
      rewrite noRejectMeansFalse xs (\e, p => noR e (There p)) in Refl
    noRejectMeansFalse (Warning :: xs) noR =
      rewrite noRejectMeansFalse xs (\e, p => noR e (There p)) in Refl
    noRejectMeansFalse (Reject  :: xs) noR =
      void (noR Reject Here Refl)

-- ════════════════════════════════════════════════════════════════════════════
-- ABI Layout declarations  (for Zig/Rust bridge validation)
-- ════════════════════════════════════════════════════════════════════════════

||| C function name exported by the SPARK/Ada layer (via Zig shim).
public export
sparkEnforcePolicySymbol : String
sparkEnforcePolicySymbol = "echidna_spark_enforce_policy"

||| C function name for worst-danger query.
public export
sparkWorstDangerSymbol : String
sparkWorstDangerSymbol = "echidna_spark_worst_danger"

||| Maximum array size accepted by the C bridge.
||| Must match Axiom_Policy.Max_Usages in src/ada/spark/axiom_policy.ads.
public export
maxUsages : Nat
maxUsages = 1024
