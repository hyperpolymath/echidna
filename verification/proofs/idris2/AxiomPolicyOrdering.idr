-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- AxiomPolicyOrdering.idr
--
-- Stage 8a meta-proof: Axiom-Policy Ordering.
--
-- Models AxiomPolicy (axiom_tracker.rs lines 44-53) as a 4-variant inductive
-- type and proves:
--
--   worstDanger_Clean      : worstDanger Clean            ≡ Safe
--   worstDanger_Classical  : worstDanger (ClassicalAxioms xs) ≡ Noted
--   worstDanger_Incomplete : worstDanger (IncompleteProof xs) ≡ Warning
--   worstDanger_Rejected   : worstDanger (Rejected xs)        ≡ Reject
--   isAcceptable_sound     : isAcceptable p ↔ worstDanger p ≠ Reject
--   danger_order_preserved : Clean ≤ ClassicalAxioms ≤ IncompleteProof ≤ Rejected
--                            under the policy danger ordering
--
-- Axiom lists are abstracted as List String (matching AxiomUsage.construct).
-- All proofs by structural induction / case analysis. Zero believe_me.

module AxiomPolicyOrdering

%default total

-- ==========================================================================
-- Section 1: DangerLevel (4-element totally ordered type)
-- ==========================================================================

||| Mirrors DangerLevel from axiom_tracker.rs.
||| Ordering: Safe < Noted < Warning < Reject.
public export
data DangerLevel = Safe | Noted | Warning | Reject

||| Numeric encoding for the order (Safe=0, Noted=1, Warning=2, Reject=3).
public export
dangerToNat : DangerLevel -> Nat
dangerToNat Safe    = 0
dangerToNat Noted   = 1
dangerToNat Warning = 2
dangerToNat Reject  = 3

||| Order on DangerLevel via dangerToNat LTE.
public export
DangerLTE : DangerLevel -> DangerLevel -> Type
DangerLTE a b = dangerToNat a `LTE` dangerToNat b

-- ==========================================================================
-- Section 2: AxiomPolicy
-- ==========================================================================

||| Mirrors AxiomPolicy from axiom_tracker.rs lines 44-53.
||| Axiom usage lists are abstracted as `List String`.
public export
data AxiomPolicy : Type where
  ||| Proof is clean — only standard axioms used.
  Clean            : AxiomPolicy
  ||| Proof has noted classical axiom usage.
  ClassicalAxioms  : List String -> AxiomPolicy
  ||| Proof has incomplete markers (sorry / Admitted).
  IncompleteProof  : List String -> AxiomPolicy
  ||| Proof uses known unsound constructs — REJECTED.
  Rejected         : List String -> AxiomPolicy

-- ==========================================================================
-- Section 3: worstDanger (mirrors AxiomPolicy::worst_danger in Rust)
-- ==========================================================================

||| Returns the worst danger level of an AxiomPolicy, exactly matching
||| axiom_tracker.rs lines 62-69.
public export
worstDanger : AxiomPolicy -> DangerLevel
worstDanger Clean                = Safe
worstDanger (ClassicalAxioms  _) = Noted
worstDanger (IncompleteProof  _) = Warning
worstDanger (Rejected         _) = Reject

-- ==========================================================================
-- Section 4: worstDanger equalities (E ≡ F notation uses _≡_ = PropEq)
-- ==========================================================================

||| worstDanger_Clean: Clean maps to Safe.
public export
worstDanger_Clean : worstDanger Clean = Safe
worstDanger_Clean = Refl

||| worstDanger_Classical: ClassicalAxioms maps to Noted.
public export
worstDanger_Classical : (xs : List String) -> worstDanger (ClassicalAxioms xs) = Noted
worstDanger_Classical _ = Refl

||| worstDanger_Incomplete: IncompleteProof maps to Warning.
public export
worstDanger_Incomplete : (xs : List String) -> worstDanger (IncompleteProof xs) = Warning
worstDanger_Incomplete _ = Refl

||| worstDanger_Rejected: Rejected maps to Reject.
public export
worstDanger_Rejected : (xs : List String) -> worstDanger (Rejected xs) = Reject
worstDanger_Rejected _ = Refl

-- ==========================================================================
-- Section 5: isAcceptable (mirrors AxiomPolicy::is_acceptable in Rust)
-- ==========================================================================

||| Mirrors AxiomPolicy::is_acceptable (axiom_tracker.rs lines 56-58).
||| A policy is acceptable iff it is not Rejected.
public export
isAcceptable : AxiomPolicy -> Bool
isAcceptable (Rejected _) = False
isAcceptable _            = True

-- ==========================================================================
-- Section 6: isAcceptable_sound — iff worst danger is not Reject
-- ==========================================================================

||| Forward direction: if isAcceptable p = True then worstDanger p ≠ Reject.
public export
isAcceptable_sound_fwd
  : (p : AxiomPolicy)
  -> isAcceptable p = True
  -> worstDanger p = Reject
  -> Void
isAcceptable_sound_fwd Clean              _    Refl impossible
isAcceptable_sound_fwd (ClassicalAxioms _) _    Refl impossible
isAcceptable_sound_fwd (IncompleteProof _) _    Refl impossible
isAcceptable_sound_fwd (Rejected _)       pf   _    = absurd pf

||| Backward direction: if worstDanger p ≠ Reject then isAcceptable p = True.
public export
isAcceptable_sound_bwd
  : (p : AxiomPolicy)
  -> (worstDanger p = Reject -> Void)
  -> isAcceptable p = True
isAcceptable_sound_bwd Clean               _   = Refl
isAcceptable_sound_bwd (ClassicalAxioms _) _   = Refl
isAcceptable_sound_bwd (IncompleteProof _) _   = Refl
isAcceptable_sound_bwd (Rejected _)        pf  = absurd (pf Refl)

||| Converse: if isAcceptable p = False then worstDanger p = Reject.
public export
notAcceptable_implies_Reject
  : (p : AxiomPolicy)
  -> isAcceptable p = False
  -> worstDanger p = Reject
notAcceptable_implies_Reject Clean               pf = absurd pf
notAcceptable_implies_Reject (ClassicalAxioms _) pf = absurd pf
notAcceptable_implies_Reject (IncompleteProof _) pf = absurd pf
notAcceptable_implies_Reject (Rejected _)        _  = Refl

-- ==========================================================================
-- Section 7: Policy danger ordering preserved
-- ==========================================================================
-- We prove Clean ≤ ClassicalAxioms ≤ IncompleteProof ≤ Rejected under
-- DangerLTE composed with worstDanger.

||| Clean ≤ ClassicalAxioms: Safe ≤ Noted.
public export
danger_order_clean_classical : DangerLTE (worstDanger Clean) (worstDanger (ClassicalAxioms []))
danger_order_clean_classical = LTEZero

||| ClassicalAxioms ≤ IncompleteProof: Noted ≤ Warning.
public export
danger_order_classical_incomplete : DangerLTE (worstDanger (ClassicalAxioms [])) (worstDanger (IncompleteProof []))
danger_order_classical_incomplete = LTESucc LTEZero

||| IncompleteProof ≤ Rejected: Warning ≤ Reject.
public export
danger_order_incomplete_rejected : DangerLTE (worstDanger (IncompleteProof [])) (worstDanger (Rejected []))
danger_order_incomplete_rejected = LTESucc (LTESucc LTEZero)

||| Full chain: Clean ≤ ClassicalAxioms ≤ IncompleteProof ≤ Rejected.
||| Proved by transitivity of LTE on the numeric encoding.
public export
danger_order_preserved : DangerLTE (worstDanger Clean) (worstDanger (Rejected []))
danger_order_preserved = LTEZero

-- ==========================================================================
-- Section 8: worstDanger is injective on the ordering (monotone)
-- ==========================================================================

||| worstDanger is non-decreasing along the canonical policy chain:
||| any two policies p ≤ q in the chain satisfy
||| DangerLTE (worstDanger p) (worstDanger q).
|||
||| We enumerate all pairs instead of introducing a separate ordering type,
||| keeping the proof constructive and explicitly exhaustive.
public export
data PolicyLE : AxiomPolicy -> AxiomPolicy -> Type where
  PE_cc   : PolicyLE Clean Clean
  PE_cls  : PolicyLE Clean (ClassicalAxioms xs)
  PE_ci   : PolicyLE Clean (IncompleteProof xs)
  PE_cr   : PolicyLE Clean (Rejected xs)
  PE_cc2  : PolicyLE (ClassicalAxioms xs) (ClassicalAxioms ys)
  PE_cli  : PolicyLE (ClassicalAxioms xs) (IncompleteProof ys)
  PE_clr  : PolicyLE (ClassicalAxioms xs) (Rejected ys)
  PE_ii   : PolicyLE (IncompleteProof xs) (IncompleteProof ys)
  PE_ir   : PolicyLE (IncompleteProof xs) (Rejected ys)
  PE_rr   : PolicyLE (Rejected xs) (Rejected ys)

||| Proof that PolicyLE implies DangerLTE on worstDanger images.
public export
policyLE_danger_mono
  : {p : AxiomPolicy}
  -> {q : AxiomPolicy}
  -> PolicyLE p q
  -> DangerLTE (worstDanger p) (worstDanger q)
policyLE_danger_mono PE_cc   = LTEZero
policyLE_danger_mono PE_cls  = LTEZero
policyLE_danger_mono PE_ci   = LTEZero
policyLE_danger_mono PE_cr   = LTEZero
policyLE_danger_mono PE_cc2  = LTESucc LTEZero
policyLE_danger_mono PE_cli  = LTESucc LTEZero
policyLE_danger_mono PE_clr  = LTESucc LTEZero
policyLE_danger_mono PE_ii   = LTESucc (LTESucc LTEZero)
policyLE_danger_mono PE_ir   = LTESucc (LTESucc LTEZero)
policyLE_danger_mono PE_rr   = LTESucc (LTESucc (LTESucc LTEZero))

-- ==========================================================================
-- Section 9: No policy maps Clean to Reject or vice versa
-- ==========================================================================

||| worstDanger Clean = Reject is uninhabited.
public export
cleanNotReject : worstDanger Clean = Reject -> Void
cleanNotReject Refl impossible

||| worstDanger (Rejected xs) = Safe is uninhabited.
public export
rejectedNotSafe : (xs : List String) -> worstDanger (Rejected xs) = Safe -> Void
rejectedNotSafe _ Refl impossible
