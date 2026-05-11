-- SPDX-License-Identifier: PMPL-1.0-or-later
--
-- Proof obligations and gnatprove discharge notes for certificates.
-- This file compiles to a no-op; all content is documentary.
--
-- Run proof:
--   cd spark/certificates
--   gnatprove --mode=prove --level=1 -P certificates.gpr

pragma SPARK_Mode (Off);

-- ════════════════════════════════════════════════════════════════════════
-- Proof obligation catalogue
-- ════════════════════════════════════════════════════════════════════════

-- PO-1  Certificate_Format / Format_Extension enumeration totality
-- ─────────────────────────────────────────────────────────────────────
-- Ada 2022 LRM 3.5.1.  Definitional, no VC.
-- Status: DEFINITIONAL.

-- PO-2  Get_Format_Extension — exhaustive case-arm Post
-- ─────────────────────────────────────────────────────────────────────
-- VC: result matches the case arm corresponding to the input F.
--
-- Discharge: the body is a six-arm case with one return per arm; each
-- return matches exactly one Post case-arm.  gnatprove substitutes the
-- path condition at the return site.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-3  Check_Alethe_Step expression function — Post
-- ─────────────────────────────────────────────────────────────────────
-- Expression function body IS the Post; definitional.
-- Status: DEFINITIONAL.

-- PO-4  Verify_Alethe expression function — Post
-- ─────────────────────────────────────────────────────────────────────
-- Expression function body IS the Post; definitional.
-- Status: DEFINITIONAL.

-- PO-5  Has_Malformed expression function — Post
-- ─────────────────────────────────────────────────────────────────────
-- Expression function body IS the Post; definitional.
-- Status: DEFINITIONAL.

-- PO-6  Cap_At_Malformed ghost lemma
-- ─────────────────────────────────────────────────────────────────────
-- VC: Has_Malformed (S) => ¬Verify_Alethe (S)
--
-- Discharge: by definition,
--   Has_Malformed (S)  ≡ (exists I in S'Range, ¬Check_Alethe_Step (S(I)))
--   Verify_Alethe  (S) ≡ (forall I in S'Range,  Check_Alethe_Step (S(I)))
-- so Has_Malformed (S) ≡ ¬Verify_Alethe (S) by ¬∀ ↔ ∃¬.
-- CVC5/Z3 close via quantifier instantiation.
-- Tactic: --level=1.
-- Status: AUTO.

-- PO-7  Empty_Verifies ghost lemma
-- ─────────────────────────────────────────────────────────────────────
-- VC: Steps'Length = 0 => Verify_Alethe (Steps)
--
-- Discharge: (forall I in empty_range, P(I)) = True is a standard SMT
-- axiom for the empty range; gnatprove closes immediately.
-- Tactic: --level=0.
-- Status: AUTO.

-- PO-8  Format_Extension_Is_Injective ghost lemma
-- ─────────────────────────────────────────────────────────────────────
-- VC: F1 /= F2 => Get_Format_Extension (F1) /= Get_Format_Extension (F2)
--
-- Discharge: case-split on F1 (six arms); within each arm,
-- Get_Format_Extension (F1) is pinned to a specific Format_Extension by
-- the case-arm Post.  F2 /= F1 means F2 falls in a different arm,
-- yielding a different Format_Extension.  Six arms × five remaining
-- choices = 30 unsat sub-cases; gnatprove enumerates and closes each
-- by direct evaluation.
-- Tactic: --level=1.
-- Status: AUTO.

-- ════════════════════════════════════════════════════════════════════════
-- Equivalence argument: SPARK spec <=> Rust implementation
-- ════════════════════════════════════════════════════════════════════════
--
-- Mirrored decisions
--   - CertificateFormat enum (6 variants, same positional order)
--   - format_extension's six-arm match (Rust line 253-262)
--   - check_alethe_step's two-arm match on AletheStepKind (Rust line
--     230-233), with the per-arm boolean predicates extracted as the
--     Raw_Is_Nonempty / Has_Rule_Marker abstractions
--   - verify_alethe's "scan all, any failure ⇒ invalid" decision
--     (Rust line 103-109), expressed as a universal quantifier
--
-- Out of scope (cannot be modeled in SPARK)
--   - DRAT/LRAT verification (Rust line 127-179): shells out to
--     drat-trim, depends on filesystem + subprocess + lossy parse of
--     stdout for "VERIFIED" substring.
--   - Lean4 / Coq kernel checks: also subprocess-based.
--   - Alethe parse_alethe_steps (Rust line 200-223): string-level
--     line.starts_with predicates; SPARK abstracts the result of
--     parsing into AletheStep records with the two booleans set.
--   - BLAKE3 hashing in ProofCertificate::new: opaque crypto.
--
-- Equivalence to the Rust verify_alethe is thus partial:
--   - Strong equivalence over the structural validator (PO-3 + PO-4
--     + PO-6 together encode the exact Rust decision function).
--   - The string-to-AletheStep adapter on the Rust side must compute
--     Raw_Is_Nonempty and Has_Rule_Marker faithfully; this is a
--     boundary obligation enforced by the AletheStep constructor on
--     the Rust side, not by SPARK.

procedure Certificates_Proof is
begin
   null;
end Certificates_Proof;
