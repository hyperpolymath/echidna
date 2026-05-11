-- SPDX-License-Identifier: PMPL-1.0-or-later
--
-- Proof obligations and gnatprove discharge notes for solver_integrity.
-- This file compiles to a no-op; all content is documentary.
--
-- Run proof:
--   cd spark/solver_integrity
--   gnatprove --mode=prove --level=1 -P solver_integrity.gpr
--
-- Expected: all VCs discharged at --level=1 with no manual lemmas.

pragma SPARK_Mode (Off);

-- ════════════════════════════════════════════════════════════════════════
-- Proof obligation catalogue
-- ════════════════════════════════════════════════════════════════════════

-- PO-1  Integrity_Status enumeration totality
-- ─────────────────────────────────────────────────────────────────────
-- Source: Ada 2022 LRM 3.5.1 — enumeration types are total over their
--         declared values.  Automatically axiomatic; no VC generated.
-- Tactic: none required.
-- Status: DEFINITIONAL (no VC).

-- PO-2  Classify_Verification — Verified branch
-- ─────────────────────────────────────────────────────────────────────
-- VC: result = Verified =>
--       Binary_Found and not Expected_Is_Placeholder
--       and Compute_Succeeded and Hashes_Match
--
-- Discharge path:
--   Only one `return Verified;` site (Rust line 279 mirror), reached when
--   Binary_Found ∧ ¬Placeholder ∧ Compute_Succeeded ∧ Hashes_Match.
--   gnatprove substitutes the path condition at the return site and
--   matches the case-arm predicate directly.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-3  Classify_Verification — Tampered branch (LOAD-BEARING)
-- ─────────────────────────────────────────────────────────────────────
-- VC: result = Tampered =>
--       Binary_Found and not Expected_Is_Placeholder
--       and Compute_Succeeded and not Hashes_Match
--
-- This is the formal restatement of issue #40's roadmap obligation:
-- "SHAKE3-512 + BLAKE3 binary integrity (hash mismatch ⇒ Failed)".
--
-- Discharge path:
--   Only one `return Tampered;` site (Rust line 285 mirror), reached
--   when the four prior if-arms all fall through.  Path condition is
--   exactly the case-arm predicate.  Closes by direct substitution.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-4  Classify_Verification — Uninitialized branch
-- ─────────────────────────────────────────────────────────────────────
-- VC: result = Uninitialized =>
--       Binary_Found and Expected_Is_Placeholder
--
-- Discharge: only `return Uninitialized;` (Rust line 257 mirror) reached
-- when Binary_Found ∧ Placeholder.  Direct substitution.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-5  Classify_Verification — Missing branch (binary not found)
-- ─────────────────────────────────────────────────────────────────────
-- VC: result = Missing  =>
--       (not Binary_Found)
--       or (Binary_Found and not Expected_Is_Placeholder
--           and not Compute_Succeeded)
--
-- Two `return Missing;` sites:
--   (a) Rust line 222 mirror — ¬Binary_Found
--   (b) Rust line 302 mirror — Binary_Found ∧ ¬Placeholder ∧ ¬Compute
-- gnatprove handles both paths as a disjunction.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-6  Classify_Verification — never returns Unchecked
-- ─────────────────────────────────────────────────────────────────────
-- VC: result = Unchecked => False
--
-- Discharge: no `return Unchecked;` in the body, so the path predicate
-- is unsatisfiable.  CVC5/Z3 closes immediately.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-7  Is_Safe expression function — Post
-- ─────────────────────────────────────────────────────────────────────
-- Expression function body IS the post-condition; no separate VC.
-- Tactic: none.
-- Status: DEFINITIONAL.

-- PO-8  Quick_Reverify — Unchanged ⇔ Cached_Match
-- ─────────────────────────────────────────────────────────────────────
-- VC: result = Unchanged  <=>  Cached_Match
--
-- Discharge: two return paths trivially partition the boolean input.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-9  Aggregate_Safe expression function — Post
-- ─────────────────────────────────────────────────────────────────────
-- Expression function body IS the post-condition; no separate VC.
-- Tactic: none.
-- Status: DEFINITIONAL.

-- PO-10  Cap_At_Tampered (ghost lemma)
-- ─────────────────────────────────────────────────────────────────────
-- VC: Has_Tampered (S) => not Aggregate_Safe (S)
--
-- Discharge path (logical chain):
--   Has_Tampered (S)
--     ≡ (exists I, S(I) = Tampered)            (by Has_Tampered defn)
--     => (exists I, not Is_Safe (S(I)))        (Is_Safe (Tampered) = False)
--     => not (forall I, Is_Safe (S(I)))        (¬∀ ≡ ∃¬)
--     ≡ not Aggregate_Safe (S)                 (by Aggregate_Safe defn).
-- CVC5/Z3 closes via quantifier instantiation + propositional reasoning.
-- Tactic: --level=1.
-- Status: AUTO.

-- PO-11  Hash_Mismatch_Means_Tampered (ghost lemma)
-- ─────────────────────────────────────────────────────────────────────
-- VC: Pre  =  Binary_Found ∧ ¬Expected_Is_Placeholder
--           ∧ Compute_Succeeded ∧ ¬Hashes_Match
--     Post =  Classify_Verification (...) = Tampered
--
-- Discharge: the Pre is exactly the case-arm condition for Tampered in
-- Classify_Verification's Post, and the case arms are mutually exclusive,
-- so substituting Pre into Classify_Verification's Post forces the
-- Tampered branch.  Closes by direct application.
-- Tactic: --level=1.
-- Status: AUTO.

-- ════════════════════════════════════════════════════════════════════════
-- Equivalence argument: SPARK spec <=> Rust implementation
-- ════════════════════════════════════════════════════════════════════════
--
-- Both implementations apply the same five-stage decision pipeline:
--   1. Try to locate the solver binary on disk.
--   2. If it's there but the manifest hash is a placeholder, mark
--      Uninitialized and compute the initial hash for future runs.
--   3. Compute the SHAKE3-512 hash; on failure, treat as Missing.
--   4. Compare the computed hash byte-for-byte against the manifest.
--   5. Equal => Verified, unequal => Tampered.
--
-- SPARK abstracts the IO and cryptographic operations into the four
-- boolean inputs of Classify_Verification.  The crypto guarantees are
-- inherited from the tiny_keccak (SHAKE3) and blake3 crates; SPARK's
-- contribution is proving the *decision tree above the crypto layer*
-- is correct and that hash mismatch unambiguously yields Tampered.
--
-- For the multi-solver verify_all path (Rust line 164-209), the SPARK
-- model is Aggregate_Safe / Has_Tampered: a fleet is safe iff every
-- member is safe, and Cap_At_Tampered proves any single Tampered
-- member is sufficient to flip the aggregate to unsafe.

procedure Solver_Integrity_Proof is
begin
   null;  -- documentary only; proof driven by solver_integrity.ads/.adb
end Solver_Integrity_Proof;
