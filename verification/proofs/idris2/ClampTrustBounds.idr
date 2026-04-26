-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ClampTrustBounds.idr
--
-- Stage 8a meta-proof: Clamp Trust Bounds.
--
-- Models clamp_trust : Nat → TrustLevel, the function that maps a raw
-- numeric score into the bounded TrustLevel range [Level1..Level5].
--
-- Proves:
--   clamp_lower_bound : ∀ n, trustValue (clamp_trust n) ≥ 1
--   clamp_upper_bound : ∀ n, trustValue (clamp_trust n) ≤ 5
--   clamp_monotone    : n ≤ m → clamp_trust n ≤ clamp_trust m (TrustLevel order)
--   clamp_fixed_points: clamp_trust 1 = Level1
--                       clamp_trust 5 = Level5
--                       clamp_trust 10 = Level5
--
-- TrustLevel is a 5-constructor data type.
-- trustValue : TrustLevel → Nat encodes the numeric value 1..5.
-- clamp_trust : Nat → TrustLevel is defined by guarded cases.
-- All proofs by case-split + decidability on Nat. Zero believe_me.

module ClampTrustBounds

import Data.Nat

%default total

-- ==========================================================================
-- Section 1: TrustLevel
-- ==========================================================================

||| 5-element trust hierarchy. Constructors in order Level1 < Level2 < … < Level5.
public export
data TrustLevel
  = Level1   -- 1
  | Level2   -- 2
  | Level3   -- 3
  | Level4   -- 4
  | Level5   -- 5

||| Numeric encoding (1–5).
public export
trustValue : TrustLevel -> Nat
trustValue Level1 = 1
trustValue Level2 = 2
trustValue Level3 = 3
trustValue Level4 = 4
trustValue Level5 = 5

-- ==========================================================================
-- Section 2: TrustLevel ordering via trustValue
-- ==========================================================================

||| TrustLTE: a ≤ b iff trustValue a ≤ trustValue b.
public export
TrustLTE : TrustLevel -> TrustLevel -> Type
TrustLTE a b = trustValue a `LTE` trustValue b

-- ==========================================================================
-- Section 3: clamp_trust definition
-- ==========================================================================

||| Maps a raw Nat score into TrustLevel, clamping to [Level1..Level5].
|||
||| Mapping:
|||   0   → Level1  (below minimum: treat as minimum trust)
|||   1   → Level1
|||   2   → Level2
|||   3   → Level3
|||   4   → Level4
|||   ≥5  → Level5
|||
||| This is an Idris2 model of the Rust trust clamping semantics.
public export
clamp_trust : Nat -> TrustLevel
clamp_trust 0             = Level1
clamp_trust 1             = Level1
clamp_trust 2             = Level2
clamp_trust 3             = Level3
clamp_trust 4             = Level4
clamp_trust (S (S (S (S (S _))))) = Level5

-- ==========================================================================
-- Section 4: clamp_lower_bound
-- ==========================================================================

||| For all n, trustValue (clamp_trust n) ≥ 1.
|||
||| Proof: case-split on n.  Each constructor of clamp_trust produces a
||| TrustLevel whose trustValue ≥ 1 by direct computation.
public export
clamp_lower_bound : (n : Nat) -> 1 `LTE` trustValue (clamp_trust n)
clamp_lower_bound 0                     = LTESucc LTEZero
clamp_lower_bound 1                     = LTESucc LTEZero
clamp_lower_bound 2                     = LTESucc LTEZero
clamp_lower_bound 3                     = LTESucc LTEZero
clamp_lower_bound 4                     = LTESucc LTEZero
clamp_lower_bound (S (S (S (S (S _))))) = LTESucc LTEZero

-- ==========================================================================
-- Section 5: clamp_upper_bound
-- ==========================================================================

||| For all n, trustValue (clamp_trust n) ≤ 5.
|||
||| Proof: case-split on n.  Each constructor of clamp_trust produces a
||| TrustLevel whose trustValue ≤ 5 by direct computation.
public export
clamp_upper_bound : (n : Nat) -> trustValue (clamp_trust n) `LTE` 5
clamp_upper_bound 0                     = LTESucc LTEZero
clamp_upper_bound 1                     = LTESucc LTEZero
clamp_upper_bound 2                     = LTESucc (LTESucc LTEZero)
clamp_upper_bound 3                     = LTESucc (LTESucc (LTESucc LTEZero))
clamp_upper_bound 4                     = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))
clamp_upper_bound (S (S (S (S (S _))))) = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

-- ==========================================================================
-- Section 6: clamp_monotone
-- ==========================================================================
-- We prove: n ≤ m → TrustLTE (clamp_trust n) (clamp_trust m).
-- Strategy: enumerate all cases where n ≤ m can hold for n,m ∈ {0,1,2,3,4,≥5}.
-- We define a helper that computes TrustLTE for each pair via a decision table.

||| Helper: for each value of clamp_trust applied to n ≤ 4, the resulting
||| TrustLevel is at most the TrustLevel for n+1 (the next step up).
||| We establish the full monotonicity table by induction on the LTE witness.

-- We first need a characterisation: clamp_trust is non-decreasing
-- as a function of Nat.  We establish this by the observation that
-- the clamp_trust function partitions Nat into 6 intervals and the
-- TrustLevel image is weakly increasing across interval boundaries.

||| A representation lemma: every Nat lands in exactly one of five zones.
||| zone 0 = {0,1}, zone 1 = {2}, zone 2 = {3}, zone 3 = {4}, zone 4 = {≥5}.
public export
data ClampZone : Nat -> Type where
  Zone01   : (n : Nat) -> n `LTE` 1    -> ClampZone n
  Zone2    : ClampZone 2
  Zone3    : ClampZone 3
  Zone4    : ClampZone 4
  Zone5up  : (n : Nat) -> 5 `LTE` n    -> ClampZone n

||| Every Nat inhabits a ClampZone.
public export
classifyNat : (n : Nat) -> ClampZone n
classifyNat 0                     = Zone01 0 LTEZero
classifyNat 1                     = Zone01 1 (LTESucc LTEZero)
classifyNat 2                     = Zone2
classifyNat 3                     = Zone3
classifyNat 4                     = Zone4
classifyNat (S (S (S (S (S k))))) = Zone5up (S (S (S (S (S k))))) (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))

||| clamp_trust is constant on zone 0 (returns Level1 for 0 and 1).
clampZone01 : (n : Nat) -> n `LTE` 1 -> clamp_trust n = Level1
clampZone01 0 _              = Refl
clampZone01 1 _              = Refl
clampZone01 (S (S _)) pf     = absurd pf

||| clamp_trust returns Level5 for all n ≥ 5.
clampZone5up : (n : Nat) -> 5 `LTE` n -> clamp_trust n = Level5
clampZone5up 0                    pf = absurd pf
clampZone5up 1                    pf = absurd pf
clampZone5up 2                    pf = absurd pf
clampZone5up 3                    pf = absurd pf
clampZone5up 4                    pf = absurd pf
clampZone5up (S (S (S (S (S _))))) _ = Refl

-- TrustLTE lemmas for adjacent levels (used to build the monotonicity table).

l1lteL1 : TrustLTE Level1 Level1
l1lteL1 = LTESucc LTEZero

l1lteL2 : TrustLTE Level1 Level2
l1lteL2 = LTESucc (LTESucc LTEZero)

l1lteL3 : TrustLTE Level1 Level3
l1lteL3 = LTESucc (LTESucc (LTESucc LTEZero))

l1lteL4 : TrustLTE Level1 Level4
l1lteL4 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

l1lteL5 : TrustLTE Level1 Level5
l1lteL5 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

l2lteL2 : TrustLTE Level2 Level2
l2lteL2 = LTESucc (LTESucc LTEZero)

l2lteL3 : TrustLTE Level2 Level3
l2lteL3 = LTESucc (LTESucc (LTESucc LTEZero))

l2lteL4 : TrustLTE Level2 Level4
l2lteL4 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

l2lteL5 : TrustLTE Level2 Level5
l2lteL5 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

l3lteL3 : TrustLTE Level3 Level3
l3lteL3 = LTESucc (LTESucc (LTESucc LTEZero))

l3lteL4 : TrustLTE Level3 Level4
l3lteL4 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

l3lteL5 : TrustLTE Level3 Level5
l3lteL5 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

l4lteL4 : TrustLTE Level4 Level4
l4lteL4 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

l4lteL5 : TrustLTE Level4 Level5
l4lteL5 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

l5lteL5 : TrustLTE Level5 Level5
l5lteL5 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

||| clamp_monotone: n ≤ m → TrustLTE (clamp_trust n) (clamp_trust m).
|||
||| Proof strategy: use classifyNat on both n and m.  For each combination of
||| zones (z_n, z_m) reachable under n ≤ m, compute clamp_trust using the zone
||| characterisation lemmas and supply the appropriate TrustLTE witness.
||| (Zone pairs where z_n > z_m are impossible under n ≤ m and are discharged
||| by absurd on the LTE hypotheses.)
public export
clamp_monotone : (n : Nat) -> (m : Nat) -> n `LTE` m -> TrustLTE (clamp_trust n) (clamp_trust m)
-- Both in zone 0/1 (≤ 1): clamp_trust n = Level1 = clamp_trust m.
clamp_monotone 0 0 _              = l1lteL1
clamp_monotone 0 1 _              = l1lteL1
clamp_monotone 1 1 _              = l1lteL1
-- n in zone 0/1, m in zone 2:
clamp_monotone 0 2 _              = l1lteL2
clamp_monotone 1 2 _              = l1lteL2
-- n in zone 0/1, m in zone 3:
clamp_monotone 0 3 _              = l1lteL3
clamp_monotone 1 3 _              = l1lteL3
-- n in zone 0/1, m in zone 4:
clamp_monotone 0 4 _              = l1lteL4
clamp_monotone 1 4 _              = l1lteL4
-- n in zone 0/1, m in zone 5+:
clamp_monotone 0 (S (S (S (S (S _))))) _  = l1lteL5
clamp_monotone 1 (S (S (S (S (S _))))) _  = l1lteL5
-- Both in zone 2:
clamp_monotone 2 2 _              = l2lteL2
-- n=2, m=3:
clamp_monotone 2 3 _              = l2lteL3
-- n=2, m=4:
clamp_monotone 2 4 _              = l2lteL4
-- n=2, m≥5:
clamp_monotone 2 (S (S (S (S (S _))))) _  = l2lteL5
-- Both zone 3:
clamp_monotone 3 3 _              = l3lteL3
-- n=3, m=4:
clamp_monotone 3 4 _              = l3lteL4
-- n=3, m≥5:
clamp_monotone 3 (S (S (S (S (S _))))) _  = l3lteL5
-- Both zone 4:
clamp_monotone 4 4 _              = l4lteL4
-- n=4, m≥5:
clamp_monotone 4 (S (S (S (S (S _))))) _  = l4lteL5
-- Both zone 5+:
clamp_monotone (S (S (S (S (S _))))) (S (S (S (S (S _))))) _ = l5lteL5
-- n > m cases: these are impossible because of the LTE hypothesis.
-- The remaining cases (m < n numerically) cannot be constructed under LTE.
clamp_monotone (S (S _)) 0 pf       = absurd pf
clamp_monotone (S (S _)) 1 pf       = absurd pf
clamp_monotone (S (S (S _))) 2 pf   = absurd pf
clamp_monotone (S (S (S (S _)))) 3 pf = absurd pf
clamp_monotone (S (S (S (S _)))) 2 pf = absurd pf
clamp_monotone (S (S (S (S (S _))))) 4 pf = absurd pf
clamp_monotone (S (S (S (S (S _))))) 3 pf = absurd pf
clamp_monotone (S (S (S (S (S _))))) 2 pf = absurd pf
clamp_monotone (S (S (S (S (S _))))) 1 pf = absurd pf
clamp_monotone (S (S (S (S (S _))))) 0 pf = absurd pf
clamp_monotone (S (S (S _))) 1 pf   = absurd pf
clamp_monotone (S (S (S _))) 0 pf   = absurd pf
clamp_monotone (S (S (S (S _)))) 1 pf = absurd pf
clamp_monotone (S (S (S (S _)))) 0 pf = absurd pf

-- ==========================================================================
-- Section 7: clamp_fixed_points
-- ==========================================================================

||| clamp_trust 1 = Level1.
public export
clamp_fp_1 : clamp_trust 1 = Level1
clamp_fp_1 = Refl

||| clamp_trust 5 = Level5.
public export
clamp_fp_5 : clamp_trust 5 = Level5
clamp_fp_5 = Refl

||| clamp_trust 10 = Level5.
public export
clamp_fp_10 : clamp_trust 10 = Level5
clamp_fp_10 = Refl

-- ==========================================================================
-- Section 8: Range corollaries
-- ==========================================================================

||| trustValue is always in the range [1,5]: combines lower and upper bounds.
public export
clamp_in_range : (n : Nat) -> (1 `LTE` trustValue (clamp_trust n), trustValue (clamp_trust n) `LTE` 5)
clamp_in_range n = (clamp_lower_bound n, clamp_upper_bound n)

||| clamp_trust is surjective onto TrustLevel (every level is hit).
public export
clamp_surjective_L1 : clamp_trust 1 = Level1
clamp_surjective_L1 = Refl

public export
clamp_surjective_L2 : clamp_trust 2 = Level2
clamp_surjective_L2 = Refl

public export
clamp_surjective_L3 : clamp_trust 3 = Level3
clamp_surjective_L3 = Refl

public export
clamp_surjective_L4 : clamp_trust 4 = Level4
clamp_surjective_L4 = Refl

public export
clamp_surjective_L5 : clamp_trust 5 = Level5
clamp_surjective_L5 = Refl
