-- SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
-- SPDX-License-Identifier: PMPL-1.0-or-later
--
-- Basic.agda — Simple proofs demonstrating fundamental logical principles.
-- Uses agda-stdlib for ℕ and propositional equality.

module Basic where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ── Identity ──────────────────────────────────────────────────────────────

-- The identity function: any proposition implies itself.
id : {A : Set} → A → A
id x = x

-- Explicit identity via lambda.
id′ : {A : Set} → A → A
id′ = λ x → x

-- Identity specialised to ℕ.
id-nat : ℕ → ℕ
id-nat = id

-- ── Function composition ─────────────────────────────────────────────────

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

infixr 9 _∘_

-- Composition associativity (definitional — both sides β-reduce to the same λ).
∘-assoc : {A B C D : Set}
        → (f : A → B) (g : B → C) (h : C → D)
        → (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
∘-assoc _ _ _ = refl
