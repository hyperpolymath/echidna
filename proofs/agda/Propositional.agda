-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Propositional.agda — intuitionistic propositional-logic proofs.

module Propositional where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Nullary using (¬_)

-- ── Basic connectives ────────────────────────────────────────────────────

-- Modus ponens.
mp : {A B : Set} → A → (A → B) → B
mp a f = f a

-- Conjunction introduction / elimination.
∧-intro : {A B : Set} → A → B → A × B
∧-intro a b = (a , b)

∧-elim₁ : {A B : Set} → A × B → A
∧-elim₁ = proj₁

∧-elim₂ : {A B : Set} → A × B → B
∧-elim₂ = proj₂

-- Disjunction introduction / elimination.
∨-introˡ : {A B : Set} → A → A ⊎ B
∨-introˡ = inj₁

∨-introʳ : {A B : Set} → B → A ⊎ B
∨-introʳ = inj₂

∨-elim : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
∨-elim f g = [ f , g ]

-- ── De Morgan (one direction, provable intuitionistically) ────────────────

-- ¬ (A ∨ B) → (¬ A) × (¬ B)
deMorgan₁ : {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
deMorgan₁ nab = (λ a → nab (inj₁ a)) , (λ b → nab (inj₂ b))

-- (¬ A) × (¬ B) → ¬ (A ∨ B)
deMorgan₂ : {A B : Set} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
deMorgan₂ (na , nb) = [ na , nb ]

-- ── Contradiction ─────────────────────────────────────────────────────────

-- From ⊥ anything follows (ex falso quodlibet).
exfalso : {A : Set} → ⊥ → A
exfalso = ⊥-elim
