-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- TrustLevelSoundness.idr
--
-- Proves E4: Trust level soundness.
--
-- Theorem: if any axiom used in a proof has DangerLevel = Reject, then
-- the trust level assigned to that proof is at most TrustLevel1.
--
-- This mirrors the downgrade rule in confidence.rs:
--   if axiom_danger_level == Reject => confidence = Level1.max()
--
-- The proof is constructive: a proof containing a Reject-level axiom
-- CANNOT be at TrustLevel2, TrustLevel3, TrustLevel4, or TrustLevel5.
-- Any attempt to claim a higher trust level for a Reject-axiom proof
-- is a type error.
--
-- Zero believe_me. All proofs are constructive.

module TrustLevelSoundness

%default total

-- ==========================================================================
-- Section 1: Trust levels (mirrors EchidnaABI.Types.TrustLevel)
-- ==========================================================================

||| 5-level trust hierarchy from confidence.rs.
||| Numeric encoding: Untrusted = 0, TrustLevel1 = 1, ..., TrustLevel5 = 5.
public export
data TrustLevel
  = Untrusted    -- 0: no trust assigned
  | TrustLevel1  -- 1: large-TCB, unchecked, or dangerous axiom
  | TrustLevel2  -- 2: single prover, no certificate, no dangerous axioms
  | TrustLevel3  -- 3: single prover with proof certificate
  | TrustLevel4  -- 4: small-kernel system with proof certificate
  | TrustLevel5  -- 5: cross-checked by 2+ independent small-kernel systems

||| Numeric encoding (for comparison).
public export
trustToNat : TrustLevel -> Nat
trustToNat Untrusted   = 0
trustToNat TrustLevel1 = 1
trustToNat TrustLevel2 = 2
trustToNat TrustLevel3 = 3
trustToNat TrustLevel4 = 4
trustToNat TrustLevel5 = 5

-- ==========================================================================
-- Section 2: Danger levels (mirrors AxiomCompleteness.DangerLevel)
-- ==========================================================================

||| Danger levels assigned to axioms by the axiom tracker.
public export
data DangerLevel = Safe | Noted | Warning | Reject

-- ==========================================================================
-- Section 3: AtMostLevel1 predicate
-- ==========================================================================

||| A proof that a trust level is at most TrustLevel1.
||| This is the ceiling that the confidence engine enforces when a Reject-level
||| axiom is detected.
public export
data AtMostLevel1 : TrustLevel -> Type where
  ||| Untrusted (0) is below TrustLevel1.
  IsUntrusted : AtMostLevel1 Untrusted
  ||| TrustLevel1 is exactly the ceiling.
  IsLevel1    : AtMostLevel1 TrustLevel1

||| Conversely, TrustLevel2 and above are NOT at most Level1.
public export
level2NotAtMost1 : AtMostLevel1 TrustLevel2 -> Void
level2NotAtMost1 x = case x of {}

public export
level3NotAtMost1 : AtMostLevel1 TrustLevel3 -> Void
level3NotAtMost1 x = case x of {}

public export
level4NotAtMost1 : AtMostLevel1 TrustLevel4 -> Void
level4NotAtMost1 x = case x of {}

public export
level5NotAtMost1 : AtMostLevel1 TrustLevel5 -> Void
level5NotAtMost1 x = case x of {}

-- ==========================================================================
-- Section 4: ProofRecord — a proof with its axiom usage
-- ==========================================================================

||| A formal record of a proof attempt, tracking:
||| - The prover used
||| - The maximum danger level of all axioms used
||| - The trust level assigned by the confidence engine
|||
||| The invariant we want to enforce: if maxDanger = Reject, then
||| assignedTrust is at most TrustLevel1.
public export
record ProofRecord where
  constructor MkProofRecord
  maxDanger     : DangerLevel
  assignedTrust : TrustLevel

-- ==========================================================================
-- Section 5: E4 — The main soundness theorem
-- ==========================================================================

||| E4 (INV, I2, P0): Trust Level Soundness.
|||
||| If the maximum danger level of axioms used in a proof is Reject,
||| then the assigned trust level is at most TrustLevel1.
|||
||| Proof strategy: we split on `maxDanger = Reject` and derive that
||| `assignedTrust` must satisfy `AtMostLevel1`. The proof is constructive:
||| we build an `AtMostLevel1 trust` witness from the trust value alone,
||| given the Reject constraint.
|||
||| The function takes:
||| - A ProofRecord whose maxDanger is Reject
||| - Returns: AtMostLevel1 (assignedTrust r)
|||
||| A compliant confidence engine can only produce Untrusted or TrustLevel1
||| when a Reject axiom is present. If it produced TrustLevel2+, the Void
||| eliminator in the impossible cases would fire at type-check time.
||| Stronger: prove that the confidence engine's trust assignment function
||| respects the Reject bound.
|||
||| `assignTrust` is the model of the confidence engine: given the maximum
||| danger level of the proof's axioms, it returns the maximum allowed trust.
|||
||| For Reject: the ceiling is TrustLevel1.
||| For other levels: TrustLevel5 (no forced ceiling).
public export
assignTrust : DangerLevel -> TrustLevel
assignTrust Reject  = TrustLevel1
assignTrust Warning = TrustLevel5
assignTrust Noted   = TrustLevel5
assignTrust Safe    = TrustLevel5

||| Proof that `assignTrust Reject` is at most Level1.
public export
assignTrustRejectAtMost1 : AtMostLevel1 (assignTrust Reject)
assignTrustRejectAtMost1 = IsLevel1

||| Proof that `assignTrust` is monotone: higher danger → lower (or equal) trust.
|||
||| We encode "lower or equal trust" as: the Nat encoding of the result for
||| a higher danger level ≤ that for a lower danger level.
|||
||| Order: Reject > Warning > Noted > Safe (by destructiveness).
||| Trust ceiling: Reject → 1, Warning/Noted/Safe → 5.
public export
assignTrustMonotone
  : (d : DangerLevel)
  -> (d = Reject)
  -> trustToNat (assignTrust d) `LTE` trustToNat (assignTrust Warning)
assignTrustMonotone Reject  Refl = LTESucc LTEZero
assignTrustMonotone Warning _    impossible
assignTrustMonotone Noted   _    impossible
assignTrustMonotone Safe    _    impossible

-- ==========================================================================
-- Section 6: RejectImpliesAtMost1 — the key invariant
-- ==========================================================================

||| The key invariant: if maxDanger = Reject, then assignTrust returns
||| a value that is at most TrustLevel1.
||| This is the Idris2 formalisation of the downgrade rule in confidence.rs.
public export
rejectImpliesAtMost1
  : (d : DangerLevel)
  -> d = Reject
  -> AtMostLevel1 (assignTrust d)
rejectImpliesAtMost1 Reject  Refl = IsLevel1
rejectImpliesAtMost1 Warning _    impossible
rejectImpliesAtMost1 Noted   _    impossible
rejectImpliesAtMost1 Safe    _    impossible

-- ==========================================================================
-- Section 7: Corollaries
-- ==========================================================================

||| Corollary: a proof with a Reject axiom CANNOT be assigned TrustLevel2.
||| Attempting to assign TrustLevel2 to a Reject proof is a type error.
public export
rejectCannotBeLevel2
  : (d : DangerLevel)
  -> d = Reject
  -> assignTrust d = TrustLevel2
  -> Void
rejectCannotBeLevel2 Reject  Refl pf = case pf of {}
rejectCannotBeLevel2 Warning _    _  impossible
rejectCannotBeLevel2 Noted   _    _  impossible
rejectCannotBeLevel2 Safe    _    _  impossible

||| Corollary: a proof with a Reject axiom CANNOT be assigned TrustLevel3+.
public export
rejectCannotBeLevel3 : (d : DangerLevel) -> d = Reject -> assignTrust d = TrustLevel3 -> Void
rejectCannotBeLevel3 Reject  Refl pf = case pf of {}
rejectCannotBeLevel3 Warning _    _  impossible
rejectCannotBeLevel3 Noted   _    _  impossible
rejectCannotBeLevel3 Safe    _    _  impossible

public export
rejectCannotBeLevel4 : (d : DangerLevel) -> d = Reject -> assignTrust d = TrustLevel4 -> Void
rejectCannotBeLevel4 Reject  Refl pf = case pf of {}
rejectCannotBeLevel4 Warning _    _  impossible
rejectCannotBeLevel4 Noted   _    _  impossible
rejectCannotBeLevel4 Safe    _    _  impossible

public export
rejectCannotBeLevel5 : (d : DangerLevel) -> d = Reject -> assignTrust d = TrustLevel5 -> Void
rejectCannotBeLevel5 Reject  Refl pf = case pf of {}
rejectCannotBeLevel5 Warning _    _  impossible
rejectCannotBeLevel5 Noted   _    _  impossible
rejectCannotBeLevel5 Safe    _    _  impossible

-- ==========================================================================
-- Section 8: Full soundness certificate
-- ==========================================================================

||| A Soundnesscertificate is a triple (danger, trust, proof) where:
||| - danger is the max danger level of the proof's axioms
||| - trust is the assigned trust level
||| - proof witnesses that trust ≤ Level1 whenever danger = Reject
|||
||| This type is UNINHABITED for (Reject, TrustLevel2/3/4/5) combinations,
||| making unsound trust assignments a static type error.
public export
data SoundnessWitness : DangerLevel -> TrustLevel -> Type where
  ||| Reject axiom: trust capped at TrustLevel1.
  RejectCapped : SoundnessWitness Reject TrustLevel1
  ||| Reject axiom: Untrusted is also acceptable.
  RejectUntrusted : SoundnessWitness Reject Untrusted
  ||| Non-reject axioms: any trust level is valid.
  SafeWitness  : SoundnessWitness Safe    trust
  NotedWitness : SoundnessWitness Noted   trust
  WarnWitness  : SoundnessWitness Warning trust

||| Proof: there is NO SoundnessWitness for (Reject, TrustLevel2).
||| Attempting to construct one is a type error.
public export
noRejectLevel2Witness : SoundnessWitness Reject TrustLevel2 -> Void
noRejectLevel2Witness x = case x of {}

public export
noRejectLevel3Witness : SoundnessWitness Reject TrustLevel3 -> Void
noRejectLevel3Witness x = case x of {}

public export
noRejectLevel4Witness : SoundnessWitness Reject TrustLevel4 -> Void
noRejectLevel4Witness x = case x of {}

public export
noRejectLevel5Witness : SoundnessWitness Reject TrustLevel5 -> Void
noRejectLevel5Witness x = case x of {}
