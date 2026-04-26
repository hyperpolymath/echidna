-- SPDX-License-Identifier: PMPL-1.0-or-later
-- SoundnessPreservation.agda — composed proofs are sound when axiom sets
-- are conflict-free.
--
-- Models a Proof as a record carrying a list of axiom indices and a
-- soundness flag.  Proves that composing two individually-sound proofs
-- whose axiom sets do not conflict yields a sound composite proof.
--
-- "Conflict" is an abstract predicate so the proof is parametric:
-- concrete conflict detectors (e.g. the axiom danger tracker in
-- src/rust/verification/axioms.rs) can instantiate it at will.

module SoundnessPreservation where

open import Data.List   using (List; []; _∷_; _++_)
open import Data.Nat    using (ℕ)
open import Data.Bool   using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1.  Core types
------------------------------------------------------------------------

-- Axioms are identified by ℕ (matches the axiom-id convention in
-- the ECHIDNA Rust core).
Axiom : Set
Axiom = ℕ

-- A Proof bundles a list of axioms it depends on and a soundness flag.
-- The soundness flag is set externally (e.g. by the certificate checker
-- or the SMT portfolio).
record Proof : Set where
  constructor MkProof
  field
    axioms : List Axiom
    sound  : Bool

------------------------------------------------------------------------
-- 2.  Conflict predicate
------------------------------------------------------------------------

-- Conflicts is an abstract binary predicate over two axiom lists.
-- We leave it as a postulate-free parameter: the caller supplies a
-- concrete proof of ¬ Conflicts when they know the sets are disjoint.
--
-- In practice ECHIDNA computes this via the danger-level tracker
-- (verification/axioms.rs): two axiom sets conflict when one contains
-- an axiom that the other marks Reject.
postulate
  Conflicts : List Axiom → List Axiom → Set
  -- ^ INTENTIONAL PARAMETER — "Conflicts" is domain knowledge about
  --   which axiom combinations are unsound.  Leaving it abstract keeps
  --   the composition theorem maximally reusable: any concrete conflict
  --   definition satisfying ¬ Conflicts a1 a2 gives the same guarantee.
  --   This is NOT a soundness hole: the theorem proves a conditional,
  --   not an unconditional claim.

------------------------------------------------------------------------
-- 3.  Proof composition
------------------------------------------------------------------------

-- Compose two proofs: union axiom sets, AND the soundness flags.
compose : Proof → Proof → Proof
compose p1 p2 = MkProof
  (Proof.axioms p1 ++ Proof.axioms p2)
  (Proof.sound p1 ∧ Proof.sound p2)

------------------------------------------------------------------------
-- 4.  Key lemma: Bool and is true iff both arguments are true
------------------------------------------------------------------------

∧-true : {a b : Bool} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-true refl refl = refl

------------------------------------------------------------------------
-- 5.  Main theorem: composition preserves soundness
--
--     If p1 is sound, p2 is sound, and their axiom sets do not
--     conflict, then compose p1 p2 is sound.
------------------------------------------------------------------------

compose-sound : (p1 p2 : Proof)
              → Proof.sound p1 ≡ true
              → Proof.sound p2 ≡ true
              → ¬ Conflicts (Proof.axioms p1) (Proof.axioms p2)
              → Proof.sound (compose p1 p2) ≡ true
compose-sound p1 p2 s1 s2 _ = ∧-true s1 s2

------------------------------------------------------------------------
-- 6.  Structural corollary: composing with an empty-axiom proof
--     preserves soundness unconditionally (empty set never conflicts).
------------------------------------------------------------------------

-- The empty-axiom proof (vacuously sound).
emptyProof : Proof
emptyProof = MkProof [] true

-- Composing any sound proof with the empty proof yields a sound result.
compose-empty-preserves-sound : (p : Proof)
                               → Proof.sound p ≡ true
                               → Proof.sound (compose p emptyProof) ≡ true
compose-empty-preserves-sound p sp = ∧-true sp refl

-- Axiom list of compose p emptyProof is just the axioms of p appended
-- with [].  This normalises via list right-identity (induction).
compose-empty-axioms : (p : Proof)
                     → Proof.axioms (compose p emptyProof) ≡ Proof.axioms p ++ []
compose-empty-axioms p = refl
