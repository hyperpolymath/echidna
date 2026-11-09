-- SPDX-License-Identifier: MPL-2.0
-- ProofComposition.agda — list-append lemmas for axiom lists.
--
-- A test fixture for the Agda backend (PROOF-POLICY §3), not evidence for
-- any obligation. It proves only that list append is associative and has a
-- left identity. It does not state or prove consistency of a union of
-- axiom sets, and it does not discharge obligation E9 (corrected
-- 2026-11-09, proof audit; see docs/PROOF-STATUS.adoc R6).

module ProofComposition where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Axioms are just indexed by ℕ.
Axiom : Set
Axiom = ℕ

-- A ProofTerm bundles a goal and its supporting axioms.
record ProofTerm : Set where
  constructor MkProof
  field
    goal   : ℕ
    axioms : List Axiom

-- Compose : merge two proof axiom-sets by list concatenation.
compose-axioms : ProofTerm → ProofTerm → List Axiom
compose-axioms p1 p2 = ProofTerm.axioms p1 ++ ProofTerm.axioms p2

-- Theorem: composition is associative over axiom concatenation.
compose-assoc : (p1 p2 p3 : ProofTerm)
              → compose-axioms (MkProof 0 (compose-axioms p1 p2)) p3
              ≡ compose-axioms p1 (MkProof 0 (compose-axioms p2 p3))
compose-assoc p1 p2 p3 = lemma (ProofTerm.axioms p1) (ProofTerm.axioms p2) (ProofTerm.axioms p3)
  where
    lemma : (as bs cs : List Axiom) → (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
    lemma []       bs cs = refl
    lemma (a ∷ as) bs cs = cong (a ∷_) (lemma as bs cs)

-- Theorem: composition preserves the length of the combined axiom set.
compose-empty-left : (p : ProofTerm)
                   → compose-axioms (MkProof 0 []) p ≡ ProofTerm.axioms p
compose-empty-left p = refl
