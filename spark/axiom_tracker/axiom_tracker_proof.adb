-- SPDX-License-Identifier: MPL-2.0
--
-- Proof obligations and gnatprove discharge notes for axiom_tracker.
-- This file compiles to a no-op; all content is documentary.
--
-- Run proof:
--   cd spark/axiom_tracker
--   gnatprove --mode=prove --level=1 -P axiom_tracker.gpr
--
-- Expected: all VCs discharged at --level=1 with no manual lemmas.

-- ════════════════════════════════════════════════════════════════════════
-- Proof obligation catalogue
-- ════════════════════════════════════════════════════════════════════════

-- PO-1  DangerLevel total order (Safe < Noted < Warning < Reject)
-- ─────────────────────────────────────────────────────────────────────
-- Source: Ada 2022 LRM 3.5.1 — enumeration ordering follows declaration
--         order.  Automatically axiomatic; no VC generated.
-- Tactic: none required.
-- Status: DEFINITIONAL (no VC).

-- PO-2  Enforce_Policy — cap-at-Reject monotonicity (post branch a)
-- ─────────────────────────────────────────────────────────────────────
-- VC: (for some J in Usages'Range => Usages(J).Danger = Reject)
--       => Enforce_Policy'Result.Kind = Rejected
--
-- Discharge path:
--   Loop_Invariant establishes at loop exit:
--     Has_Reject = (for some J in First..Last => Danger = Reject)
--   The `if Has_Reject then return (Kind => Rejected)` branch fires.
--   gnatprove substitutes the invariant equation into the post-condition
--   and closes with Z3 / CVC5 at --level=1.
-- Tactic: --level=1.
-- Status: AUTO.

-- PO-3  Enforce_Policy — Warning priority (post branch b)
-- ─────────────────────────────────────────────────────────────────────
-- VC: (all /= Reject) and (some = Warning) => Kind = Incomplete_Proof
--
-- Discharge path: analogous to PO-2 via Has_Warning invariant arm.
-- Tactic: --level=1.
-- Status: AUTO.

-- PO-4  Enforce_Policy — Noted priority (post branch c)
-- ─────────────────────────────────────────────────────────────────────
-- Analogous to PO-3 via Has_Noted invariant arm.
-- Tactic: --level=1.
-- Status: AUTO.

-- PO-5  Enforce_Policy — empty input => Clean (post branch d)
-- ─────────────────────────────────────────────────────────────────────
-- VC: Usages'Length = 0 => result.Kind = Clean
--
-- Discharge path:
--   Empty range => loop body never executes; accumulators stay False.
--   Final else-branch returns Clean.
--   SMT solver evaluates (for some J in empty_range => P) = False.
-- Tactic: --level=1.
-- Status: AUTO.

-- PO-6  Loop_Invariant establishment (first iteration, I = First)
-- ─────────────────────────────────────────────────────────────────────
-- At I = First after the case statement:
--   Has_X = (X_condition holds for Usages(First))
--          = (for some J in First..First => condition)
-- Singleton quantifier reduces to a single comparison; gnatprove closes
-- with direct substitution.
-- Tactic: --level=1.
-- Status: AUTO.

-- PO-7  Loop_Invariant preservation (inductive step, I-1 => I)
-- ─────────────────────────────────────────────────────────────────────
-- Assuming the invariant at I-1, prove it at I.
--   Has_Reject@I = Has_Reject@(I-1)  OR  Usages(I).Danger = Reject
--               = (for some J in First..I-1 => Reject) OR Usages(I) = Reject
--               = (for some J in First..I   => Reject)
-- Standard set-extension argument; CVC5 closes at --level=1.
-- Tactic: --level=1.
-- Status: AUTO.

-- PO-8  Is_Acceptable post-condition
-- ─────────────────────────────────────────────────────────────────────
-- Direct boolean equation: body returns P.Kind /= Rejected.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-9  Worst_Danger exhaustive case equation
-- ─────────────────────────────────────────────────────────────────────
-- One trivial equality VC per case arm.
-- Tactic: --level=0.
-- Status: AUTO.

-- ════════════════════════════════════════════════════════════════════════
-- Equivalence argument: SPARK spec <=> Rust implementation
-- ════════════════════════════════════════════════════════════════════════
--
-- Both implementations:
--   1. Forward-scan the input sequence.
--   2. Accumulate three boolean flags (Reject / Warning / Noted).
--   3. Apply priority chain Reject > Warning > Noted > Clean.
--   4. Return immediately from the winning branch.
--
-- The SPARK post-condition is a formal restatement of the Rust
-- doc-comment semantics.  The `enforce_policy_with_spark_crosscheck`
-- method (Rust, --features spark) calls the Ada compiled-to-C bridge
-- at runtime and panics in debug builds on divergence — defence-in-depth
-- complementing this static proof.

procedure Axiom_Tracker_Proof is
begin
   null;  -- documentary only; proof driven by axiom_tracker.ads/.adb
end Axiom_Tracker_Proof;
