-- SPDX-License-Identifier: PMPL-1.0-or-later
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
-- NO believe_me — every proof is constructive (Refl, case analysis, or
-- explicit witnesses).

module EchidnaABI.AxiomTracker

import EchidnaABI.Types   -- ProverKind, Platform, etc.
import Data.List
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

||| Specification of enforcePolicySpec: the reference function that the
||| SPARK implementation must replicate.
|||
||| This is NOT the live callable; it is the specification the bridge tests
||| against via cross-check mode.
public export
enforcePolicySpec : List DangerLevel -> AxiomPolicy
enforcePolicySpec usages =
  if any (== Reject) usages then PolicyRejected
  else if any (== Warning) usages then PolicyIncomplete
  else if any (== Noted) usages then PolicyClassical
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
  -- 'any (== Reject) usages' is True whenever Reject is an element
  rewrite anyRejectIsTrue usages prf in Refl
  where
    anyRejectIsTrue
      : (us : List DangerLevel)
      -> Elem Reject us
      -> any (== Reject) us = True
    anyRejectIsTrue (Reject :: _)  Here       = Refl
    anyRejectIsTrue (_ :: rest)    (There p)  = anyRejectIsTrue rest p
    anyRejectIsTrue []             p           = absurd p

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
  -- If enforcePolicySpec returns PolicyRejected, then 'any (== Reject) usages'
  -- must have been True, so there is a Reject in the list — contradicting noReject.
  let anyFalse = noRejectMeansAnyFalse usages noReject
  in rewrite anyFalse in absurd prf
  where
    noRejectMeansAnyFalse
      : (us : List DangerLevel)
      -> ((e : DangerLevel) -> Elem e us -> Not (e = Reject))
      -> any (== Reject) us = False
    noRejectMeansAnyFalse [] _ = Refl
    noRejectMeansAnyFalse (x :: xs) noR =
      case decEq x Reject of
        Yes Refl => absurd (noR Reject Here Refl)
        No  _    =>
          let rest = noRejectMeansAnyFalse xs (\e p => noR e (There p))
          in rewrite rest in Refl

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
