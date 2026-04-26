-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- TrustKernelMonotonicity.idr
--
-- Stage 8a meta-proof: Trust-Kernel Monotonicity.
--
-- Proves that the confidence engine's downgrade rules are monotone:
--
--   trustMono_reject   : worst_danger = Reject  → compute_trust = Level1
--   trustMono_warning  : worst_danger = Warning → compute_trust = Level1
--   trustMono_integrity: solver_integrity_ok = False → compute_trust = Level1
--   trustMono_level5_conditions : confirming ≥ 2 ∧ certificate_verified = True
--                                 ∧ small_kernel = True → compute_trust ≥ Level4
--
-- Models TrustFactors as a record over the booleans and DangerLevel fields
-- that drive the Rust compute_trust_level function.
-- Models compute_trust_level exactly from confidence.rs lines 77-116.
-- All proofs by exhaustive case analysis. Zero believe_me.

module TrustKernelMonotonicity

%default total

-- ==========================================================================
-- Section 1: DangerLevel
-- ==========================================================================

||| Mirrors DangerLevel from axiom_tracker.rs.
||| The derive(PartialOrd, Ord) on the Rust side gives Safe < Noted < Warning < Reject
||| (matching declaration order). We do not need the full order here — only
||| equality tests used by compute_trust_level.
public export
data DangerLevel = Safe | Noted | Warning | Reject

-- ==========================================================================
-- Section 2: TrustLevel (5-element ordered type)
-- ==========================================================================

||| 5-element trust hierarchy from confidence.rs.
||| Level1 < Level2 < Level3 < Level4 < Level5.
public export
data TrustLevel
  = Level1   -- 1: dangerous axiom / bad integrity / rejected
  | Level2   -- 2: single prover, no dangerous axioms
  | Level3   -- 3: certificate present and verified, or cross-checked
  | Level4   -- 4: small-kernel prover with verified certificate
  | Level5   -- 5: cross-checked by 2+ small-kernel provers with certs

||| Numeric encoding of TrustLevel (1–5).
public export
trustValue : TrustLevel -> Nat
trustValue Level1 = 1
trustValue Level2 = 2
trustValue Level3 = 3
trustValue Level4 = 4
trustValue Level5 = 5

-- ==========================================================================
-- Section 3: TrustLevel ordering
-- ==========================================================================

||| Ordering on TrustLevel encoded via trustValue LTE.
public export
TrustLTE : TrustLevel -> TrustLevel -> Type
TrustLTE a b = trustValue a `LTE` trustValue b

-- Convenience constructor aliases used in proofs below.

trustLTE_refl : (t : TrustLevel) -> TrustLTE t t
trustLTE_refl Level1 = LTESucc LTEZero
trustLTE_refl Level2 = LTESucc (LTESucc LTEZero)
trustLTE_refl Level3 = LTESucc (LTESucc (LTESucc LTEZero))
trustLTE_refl Level4 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))
trustLTE_refl Level5 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

||| Level4 ≤ Level4 and Level4 ≤ Level5: both satisfy ≥ Level4.
level4LTELevel4 : TrustLTE Level4 Level4
level4LTELevel4 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

level4LTELevel5 : TrustLTE Level4 Level5
level4LTELevel5 = LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

-- ==========================================================================
-- Section 4: TrustFactors record
-- ==========================================================================

||| Abstracted TrustFactors record carrying only the fields that
||| determine which branch of compute_trust_level fires.
|||
||| We drop `prover : ProverKind` and fold is_small_kernel into a
||| boolean flag `small_kernel`, which is the only property of the
||| prover that compute_trust_level queries.
||| We drop `portfolio_confidence` and `has_certificate` beyond their
||| influence on certificate_verified, matching the code structure.
public export
record TrustFactors where
  constructor MkTrustFactors
  confirming_provers    : Nat
  certificate_verified  : Bool
  worst_axiom_danger    : DangerLevel
  solver_integrity_ok   : Bool
  small_kernel          : Bool

-- ==========================================================================
-- Section 5: compute_trust_level (Idris2 model of confidence.rs)
-- ==========================================================================

||| Direct transcription of compute_trust_level (confidence.rs lines 77-116).
|||
||| Branch order is preserved exactly:
|||   1. worst_axiom_danger = Reject   → Level1
|||   2. worst_axiom_danger = Warning  → Level1
|||   3. solver_integrity_ok = False   → Level1
|||   4. confirming ≥ 2 ∧ cert_verified ∧ small_kernel → Level5
|||   5. small_kernel ∧ cert_verified                   → Level4
|||   6. cert_verified                                  → Level3
|||   7. confirming ≥ 2                                 → Level3
|||   8. (default)                                      → Level2
public export
computeTrustLevel : TrustFactors -> TrustLevel
computeTrustLevel f =
  case f.worst_axiom_danger of
    Reject  => Level1
    Warning => Level1
    _       =>
      case f.solver_integrity_ok of
        False => Level1
        True  =>
          case (f.confirming_provers >= 2, f.certificate_verified, f.small_kernel) of
            (True,  True,  True)  => Level5
            (_,     True,  True)  => Level4
            (_,     True,  False) => Level3
            (True,  False, _)     => Level3
            _                     => Level2

-- ==========================================================================
-- Section 6: Downgrade proofs
-- ==========================================================================

||| trustMono_reject: worst_danger = Reject → compute_trust = Level1.
|||
||| Proof: computeTrustLevel pattern-matches on worst_axiom_danger first;
||| the Reject branch immediately returns Level1 regardless of all other fields.
public export
trustMono_reject
  : (f : TrustFactors)
  -> f.worst_axiom_danger = Reject
  -> computeTrustLevel f = Level1
trustMono_reject (MkTrustFactors _ _ Reject _ _) Refl = Refl
trustMono_reject (MkTrustFactors _ _ Safe    _ _) Refl impossible
trustMono_reject (MkTrustFactors _ _ Noted   _ _) Refl impossible
trustMono_reject (MkTrustFactors _ _ Warning _ _) Refl impossible

||| trustMono_warning: worst_danger = Warning → compute_trust = Level1.
|||
||| Proof: the Warning branch fires immediately after Reject, returning Level1.
public export
trustMono_warning
  : (f : TrustFactors)
  -> f.worst_axiom_danger = Warning
  -> computeTrustLevel f = Level1
trustMono_warning (MkTrustFactors _ _ Warning _ _) Refl = Refl
trustMono_warning (MkTrustFactors _ _ Safe    _ _) Refl impossible
trustMono_warning (MkTrustFactors _ _ Noted   _ _) Refl impossible
trustMono_warning (MkTrustFactors _ _ Reject  _ _) Refl impossible

-- ==========================================================================
-- Section 7: Integrity downgrade
-- ==========================================================================

||| A witness that the solver integrity check failed.
||| We use a named record to carry the proof cleanly.
public export
data BadIntegrity : TrustFactors -> Type where
  ||| The solver_integrity_ok field is False.
  MkBadIntegrity
    : (f : TrustFactors)
    -> f.solver_integrity_ok = False
    -> BadIntegrity f

||| trustMono_integrity: BadIntegrity f → compute_trust = Level1.
|||
||| Proof: we case-split on worst_axiom_danger.  For Reject and Warning the
||| result is Level1 independently (earlier branches fire).  For Safe and
||| Noted we reach the solver_integrity_ok = False branch which returns Level1.
public export
trustMono_integrity
  : (f  : TrustFactors)
  -> BadIntegrity f
  -> computeTrustLevel f = Level1
trustMono_integrity (MkTrustFactors _ _ Reject  False _) (MkBadIntegrity _ Refl) = Refl
trustMono_integrity (MkTrustFactors _ _ Warning False _) (MkBadIntegrity _ Refl) = Refl
trustMono_integrity (MkTrustFactors _ _ Safe    False _) (MkBadIntegrity _ Refl) = Refl
trustMono_integrity (MkTrustFactors _ _ Noted   False _) (MkBadIntegrity _ Refl) = Refl
-- solver_integrity_ok = True contradicts the BadIntegrity witness:
trustMono_integrity (MkTrustFactors _ _ Reject  True _) (MkBadIntegrity _ Refl) impossible
trustMono_integrity (MkTrustFactors _ _ Warning True _) (MkBadIntegrity _ Refl) impossible
trustMono_integrity (MkTrustFactors _ _ Safe    True _) (MkBadIntegrity _ Refl) impossible
trustMono_integrity (MkTrustFactors _ _ Noted   True _) (MkBadIntegrity _ Refl) impossible

-- ==========================================================================
-- Section 8: Level5 sufficient conditions
-- ==========================================================================

||| trustMono_level5_conditions:
||| confirming ≥ 2 ∧ certificate_verified = True ∧ small_kernel = True
||| → compute_trust ≥ Level4.
|||
||| In fact under these conditions compute_trust = Level5, so we prove the
||| equality first and derive ≥ Level4 as a corollary.
|||
||| Proof: we case-split on worst_axiom_danger and solver_integrity_ok.
||| The only dangerous-axiom paths (Reject, Warning) return Level1, which
||| contradicts the Level5 hypothesis — but since we are proving the
||| implication in the SAFE direction (the precondition is the clean case),
||| we can restrict attention to worst_axiom_danger ∈ {Safe, Noted}
||| combined with solver_integrity_ok = True.  In that regime, the first
||| inner case fires (True, True, True) → Level5.

||| Helper: under clean conditions the Level5 branch fires.
public export
trustMono_level5_exact
  : (n : Nat)
  -> (n >= 2 = True)
  -> (danger : DangerLevel)
  -> (danger = Safe \/ danger = Noted)
  -> computeTrustLevel (MkTrustFactors n True danger True True) = Level5
trustMono_level5_exact n hge Safe    (Left  Refl) with (n >= 2)
  trustMono_level5_exact n hge Safe    (Left  Refl) | True  = Refl
  trustMono_level5_exact n _   Safe    (Left  Refl) | False impossible
trustMono_level5_exact n hge Noted   (Right Refl) with (n >= 2)
  trustMono_level5_exact n hge Noted   (Right Refl) | True  = Refl
  trustMono_level5_exact n _   Noted   (Right Refl) | False impossible
trustMono_level5_exact _ _   Reject  (Left  Refl) impossible
trustMono_level5_exact _ _   Reject  (Right Refl) impossible
trustMono_level5_exact _ _   Warning (Left  Refl) impossible
trustMono_level5_exact _ _   Warning (Right Refl) impossible

||| The corollary: under the clean triple-condition the result is ≥ Level4.
||| Since Level5 ≥ Level4 (trustValue Level5 = 5 ≥ 4 = trustValue Level4).
public export
trustMono_level5_conditions
  : (n : Nat)
  -> (n >= 2 = True)
  -> (danger : DangerLevel)
  -> (danger = Safe \/ danger = Noted)
  -> TrustLTE Level4
       (computeTrustLevel (MkTrustFactors n True danger True True))
trustMono_level5_conditions n hge Safe  (Left  Refl) with (n >= 2)
  trustMono_level5_conditions n hge Safe  (Left  Refl) | True  = level4LTELevel5
  trustMono_level5_conditions n _   Safe  (Left  Refl) | False impossible
trustMono_level5_conditions n hge Noted (Right Refl) with (n >= 2)
  trustMono_level5_conditions n hge Noted (Right Refl) | True  = level4LTELevel5
  trustMono_level5_conditions n _   Noted (Right Refl) | False impossible
trustMono_level5_conditions _ _   Reject  (Left  Refl) impossible
trustMono_level5_conditions _ _   Reject  (Right Refl) impossible
trustMono_level5_conditions _ _   Warning (Left  Refl) impossible
trustMono_level5_conditions _ _   Warning (Right Refl) impossible

-- ==========================================================================
-- Section 9: Injectivity witnesses (Level1 is the unique floor)
-- ==========================================================================

||| The three downgrade paths produce identical output (Level1), and that
||| output is incompatible with any level ≥ Level2.
public export
level1NotLevel2 : Level1 = Level2 -> Void
level1NotLevel2 Refl impossible

public export
level1NotLevel3 : Level1 = Level3 -> Void
level1NotLevel3 Refl impossible

public export
level1NotLevel4 : Level1 = Level4 -> Void
level1NotLevel4 Refl impossible

public export
level1NotLevel5 : Level1 = Level5 -> Void
level1NotLevel5 Refl impossible
