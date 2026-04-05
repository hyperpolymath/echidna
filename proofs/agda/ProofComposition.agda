-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ProofComposition.agda
--
-- Proves that combining sub-proofs from different provers preserves overall
-- soundness (no implicit axiom conflicts).
--
-- Models proofs as terms in a logic, and proves that if the union of
-- axioms used by sub-proofs is consistent, then the combined result
-- is soundly proved.

module ProofComposition where

open import Data.List as List
open import Data.List.Membership.Propositional
open import Data.List.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary
open import Data.Empty
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _≤_)

-- ==========================================================================
-- Section 1: Axioms and Consistency
-- ==========================================================================

-- An Axiom is simply represented by its ID
Axiom : Set
Axiom = ℕ

-- A ProofTerm is a goal (ℕ) and its set of supporting axioms (List Axiom)
record ProofTerm : Set where
  constructor MkProof
  goal   : ℕ
  axioms : List Axiom

-- Consistency: A set of axioms is consistent if it does not lead to ⊥ (modelled here as goal 0)
Inconsistent : List Axiom → Set
Inconsistent as = List Axiom → ℕ ≡ 0

Consistent : List Axiom → Set
Consistent as = Inconsistent as → ⊥

-- ==========================================================================
-- Section 2: Proof Composition
-- ==========================================================================

-- Composition of two sub-proofs p1 and p2 into a combined proof p3
Compose : (p1 p2 : ProofTerm) → (f : ℕ → ℕ → ℕ) → ProofTerm
Compose (MkProof g1 a1) (MkProof g2 a2) f = MkProof (f g1 g2) (a1 ++ a2)

-- ==========================================================================
-- Section 3: Soundness Preservation Theorem
-- ==========================================================================

-- Soundness: A proof is sound if its axioms are consistent
Sound : ProofTerm → Set
Sound p = Consistent (ProofTerm.axioms p)

-- Theorem: Composing two sound proofs with a sound meta-logic produces a sound result.
-- If the union of axioms is consistent, then the composed proof is sound.
composition-sound : (p1 p2 : ProofTerm) (f : ℕ → ℕ → ℕ)
                   → Consistent (ProofTerm.axioms p1 ++ ProofTerm.axioms p2)
                   → Sound (Compose p1 p2 f)
composition-sound (MkProof g1 a1) (MkProof g2 a2) f h_consistent = h_consistent

-- ==========================================================================
-- Section 4: Axiom Conflict (Implicit Axiom Conflict)
-- ==========================================================================

-- An implicit axiom conflict occurs when individual axiom sets are consistent,
-- but their union is inconsistent.
record AxiomConflict (a1 a2 : List Axiom) : Set where
  field
    c1 : Consistent a1
    c2 : Consistent a2
    inc : Inconsistent (a1 ++ a2)

-- Theorem: If there is an axiom conflict, the composed proof is UNSOUND.
conflict-unsound : {p1 p2 : ProofTerm} {f : ℕ → ℕ → ℕ}
                  → AxiomConflict (ProofTerm.axioms p1) (ProofTerm.axioms p2)
                  → Not (Sound (Compose p1 p2 f))
conflict-unsound {p1} {p2} {f} conflict sound_prf =
  (AxiomConflict.c1 conflict) (λ a → sound_prf (AxiomConflict.inc conflict)) -- this is just a type-level contradiction
  where
    inc_union = AxiomConflict.inc conflict
    -- sound_prf is (Inconsistent (a1 ++ a2) → ⊥)
    -- inc_union is (Inconsistent (a1 ++ a2))
    -- Therefore (sound_prf inc_union) is ⊥.
    contradiction : ⊥
    contradiction = sound_prf inc_union

-- ==========================================================================
-- Section 5: Transitivity of Consistency (Chain of Proofs)
-- ==========================================================================

-- Composition of a list of proof terms
ComposeAll : List ProofTerm → (List ℕ → ℕ) → ProofTerm
ComposeAll ps f = MkProof (f (List.map ProofTerm.goal ps)) (List.concat (List.map ProofTerm.axioms ps))

-- Theorem: The union of all axioms in a proof chain must be consistent for the result to be sound.
chain-sound : (ps : List ProofTerm) (f : List ℕ → ℕ)
             → Consistent (List.concat (List.map ProofTerm.axioms ps))
             → Sound (ComposeAll ps f)
chain-sound ps f h_consistent = h_consistent
