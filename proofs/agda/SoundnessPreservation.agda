-- SPDX-License-Identifier: MPL-2.0
-- SoundnessPreservation.agda — corpus fixture (PROOF-POLICY §3): Bool-flag
-- composition.
--
-- What it proves: if two Bool "sound" flags are true, their conjunction is
-- true. `compose-sound` takes a Conflicts hypothesis but never uses it, so
-- it says nothing about conflicting axioms and is not evidence that
-- composition preserves soundness. E9's evidence is meta-checker/src/
-- Echidna/Composition.agda, where soundness is semantic entailment and the
-- conflict check is shown to be load-bearing (`explosion`).

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

-- "Conflicts" is an abstract binary predicate over two axiom lists. It is
-- threaded as an *explicit parameter* of the composition theorem (§5)
-- rather than a module-level postulate, so this file declares ZERO axioms.
--
-- In practice ECHIDNA instantiates it via the danger-level tracker
-- (src/rust/verification/axioms.rs): two axiom sets conflict when one
-- contains an axiom the other marks Reject. The theorem proves a
-- conditional ("if the sets do not conflict …"), so any concrete conflict
-- definition gives the same guarantee.

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

compose-sound : (Conflicts : List Axiom → List Axiom → Set)
              → (p1 p2 : Proof)
              → Proof.sound p1 ≡ true
              → Proof.sound p2 ≡ true
              → ¬ Conflicts (Proof.axioms p1) (Proof.axioms p2)
              → Proof.sound (compose p1 p2) ≡ true
compose-sound _ p1 p2 s1 s2 _ = ∧-true s1 s2

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
