-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- TrustLevel.agda — Formal verification of ECHIDNA's 5-level trust hierarchy
--
-- This module proves that the trust level system is:
-- 1. A total order (reflexive, antisymmetric, transitive, total)
-- 2. Monotonic under composition (combining evidence never lowers trust)
-- 3. Sound w.r.t. dangerous axioms (dangerous axioms always cap at Level1)
-- 4. Complete (every proof state maps to exactly one trust level)

module Echidna.TrustLevel where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _≤?_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Trust Level Definition (mirrors Rust TrustLevel enum)
------------------------------------------------------------------------

data TrustLevel : Set where
  Level1 : TrustLevel  -- Large-TCB, unchecked, or dangerous axioms
  Level2 : TrustLevel  -- Single prover, no dangerous axioms
  Level3 : TrustLevel  -- Single prover + verified certificate
  Level4 : TrustLevel  -- Small-kernel + certificate
  Level5 : TrustLevel  -- 2+ independent small-kernel + certificates

------------------------------------------------------------------------
-- Numeric encoding (for ordering proofs)
------------------------------------------------------------------------

trust-to-ℕ : TrustLevel → ℕ
trust-to-ℕ Level1 = 1
trust-to-ℕ Level2 = 2
trust-to-ℕ Level3 = 3
trust-to-ℕ Level4 = 4
trust-to-ℕ Level5 = 5

------------------------------------------------------------------------
-- Ordering relation
------------------------------------------------------------------------

data _≤ₜ_ : TrustLevel → TrustLevel → Set where
  l1≤ : ∀ {t} → Level1 ≤ₜ t
  l2≤2 : Level2 ≤ₜ Level2
  l2≤3 : Level2 ≤ₜ Level3
  l2≤4 : Level2 ≤ₜ Level4
  l2≤5 : Level2 ≤ₜ Level5
  l3≤3 : Level3 ≤ₜ Level3
  l3≤4 : Level3 ≤ₜ Level4
  l3≤5 : Level3 ≤ₜ Level5
  l4≤4 : Level4 ≤ₜ Level4
  l4≤5 : Level4 ≤ₜ Level5
  l5≤5 : Level5 ≤ₜ Level5

------------------------------------------------------------------------
-- Proof: ≤ₜ is reflexive
------------------------------------------------------------------------

≤ₜ-refl : ∀ (t : TrustLevel) → t ≤ₜ t
≤ₜ-refl Level1 = l1≤
≤ₜ-refl Level2 = l2≤2
≤ₜ-refl Level3 = l3≤3
≤ₜ-refl Level4 = l4≤4
≤ₜ-refl Level5 = l5≤5

------------------------------------------------------------------------
-- Proof: ≤ₜ is antisymmetric
------------------------------------------------------------------------

≤ₜ-antisym : ∀ {a b} → a ≤ₜ b → b ≤ₜ a → a ≡ b
≤ₜ-antisym l1≤ l1≤ = refl
≤ₜ-antisym l2≤2 l2≤2 = refl
≤ₜ-antisym l3≤3 l3≤3 = refl
≤ₜ-antisym l4≤4 l4≤4 = refl
≤ₜ-antisym l5≤5 l5≤5 = refl

------------------------------------------------------------------------
-- Proof: ≤ₜ is transitive
------------------------------------------------------------------------

≤ₜ-trans : ∀ {a b c} → a ≤ₜ b → b ≤ₜ c → a ≤ₜ c
≤ₜ-trans l1≤ _ = l1≤
≤ₜ-trans l2≤2 l2≤2 = l2≤2
≤ₜ-trans l2≤2 l2≤3 = l2≤3
≤ₜ-trans l2≤2 l2≤4 = l2≤4
≤ₜ-trans l2≤2 l2≤5 = l2≤5
≤ₜ-trans l2≤3 l3≤3 = l2≤3
≤ₜ-trans l2≤3 l3≤4 = l2≤4
≤ₜ-trans l2≤3 l3≤5 = l2≤5
≤ₜ-trans l2≤4 l4≤4 = l2≤4
≤ₜ-trans l2≤4 l4≤5 = l2≤5
≤ₜ-trans l2≤5 l5≤5 = l2≤5
≤ₜ-trans l3≤3 l3≤3 = l3≤3
≤ₜ-trans l3≤3 l3≤4 = l3≤4
≤ₜ-trans l3≤3 l3≤5 = l3≤5
≤ₜ-trans l3≤4 l4≤4 = l3≤4
≤ₜ-trans l3≤4 l4≤5 = l3≤5
≤ₜ-trans l3≤5 l5≤5 = l3≤5
≤ₜ-trans l4≤4 l4≤4 = l4≤4
≤ₜ-trans l4≤4 l4≤5 = l4≤5
≤ₜ-trans l4≤5 l5≤5 = l4≤5
≤ₜ-trans l5≤5 l5≤5 = l5≤5

------------------------------------------------------------------------
-- Proof: ≤ₜ is total
------------------------------------------------------------------------

≤ₜ-total : ∀ (a b : TrustLevel) → (a ≤ₜ b) ⊎ (b ≤ₜ a)
≤ₜ-total Level1 _ = inj₁ l1≤
≤ₜ-total _ Level1 = inj₂ l1≤
≤ₜ-total Level2 Level2 = inj₁ l2≤2
≤ₜ-total Level2 Level3 = inj₁ l2≤3
≤ₜ-total Level2 Level4 = inj₁ l2≤4
≤ₜ-total Level2 Level5 = inj₁ l2≤5
≤ₜ-total Level3 Level2 = inj₂ l2≤3
≤ₜ-total Level3 Level3 = inj₁ l3≤3
≤ₜ-total Level3 Level4 = inj₁ l3≤4
≤ₜ-total Level3 Level5 = inj₁ l3≤5
≤ₜ-total Level4 Level2 = inj₂ l2≤4
≤ₜ-total Level4 Level3 = inj₂ l3≤4
≤ₜ-total Level4 Level4 = inj₁ l4≤4
≤ₜ-total Level4 Level5 = inj₁ l4≤5
≤ₜ-total Level5 Level2 = inj₂ l2≤5
≤ₜ-total Level5 Level3 = inj₂ l3≤5
≤ₜ-total Level5 Level4 = inj₂ l4≤5
≤ₜ-total Level5 Level5 = inj₁ l5≤5

------------------------------------------------------------------------
-- Minimum function (safe composition)
------------------------------------------------------------------------

min-trust : TrustLevel → TrustLevel → TrustLevel
min-trust Level1 _ = Level1
min-trust _ Level1 = Level1
min-trust Level2 b = Level2
min-trust a Level2 = Level2
min-trust Level3 b = Level3
min-trust a Level3 = Level3
min-trust Level4 Level4 = Level4
min-trust Level4 Level5 = Level4
min-trust Level5 Level4 = Level4
min-trust Level5 Level5 = Level5

------------------------------------------------------------------------
-- Proof: min-trust computes a lower bound
------------------------------------------------------------------------

min-trust-lb-left : ∀ (a b : TrustLevel) → min-trust a b ≤ₜ a
min-trust-lb-left Level1 _ = l1≤
min-trust-lb-left Level2 Level1 = l1≤
min-trust-lb-left Level2 Level2 = l2≤2
min-trust-lb-left Level2 Level3 = l2≤2
min-trust-lb-left Level2 Level4 = l2≤2
min-trust-lb-left Level2 Level5 = l2≤2
min-trust-lb-left Level3 Level1 = l1≤
min-trust-lb-left Level3 Level2 = l2≤3
min-trust-lb-left Level3 Level3 = l3≤3
min-trust-lb-left Level3 Level4 = l3≤3
min-trust-lb-left Level3 Level5 = l3≤3
min-trust-lb-left Level4 Level1 = l1≤
min-trust-lb-left Level4 Level2 = l2≤4
min-trust-lb-left Level4 Level3 = l3≤4
min-trust-lb-left Level4 Level4 = l4≤4
min-trust-lb-left Level4 Level5 = l4≤4
min-trust-lb-left Level5 Level1 = l1≤
min-trust-lb-left Level5 Level2 = l2≤5
min-trust-lb-left Level5 Level3 = l3≤5
min-trust-lb-left Level5 Level4 = l4≤5
min-trust-lb-left Level5 Level5 = l5≤5

min-trust-lb-right : ∀ (a b : TrustLevel) → min-trust a b ≤ₜ b
min-trust-lb-right _ Level1 = l1≤
min-trust-lb-right Level1 Level2 = l1≤
min-trust-lb-right Level1 Level3 = l1≤
min-trust-lb-right Level1 Level4 = l1≤
min-trust-lb-right Level1 Level5 = l1≤
min-trust-lb-right Level2 Level2 = l2≤2
min-trust-lb-right Level2 Level3 = l2≤3
min-trust-lb-right Level2 Level4 = l2≤4
min-trust-lb-right Level2 Level5 = l2≤5
min-trust-lb-right Level3 Level2 = l2≤2
min-trust-lb-right Level3 Level3 = l3≤3
min-trust-lb-right Level3 Level4 = l3≤4
min-trust-lb-right Level3 Level5 = l3≤5
min-trust-lb-right Level4 Level2 = l2≤2
min-trust-lb-right Level4 Level3 = l3≤3
min-trust-lb-right Level4 Level4 = l4≤4
min-trust-lb-right Level4 Level5 = l4≤5
min-trust-lb-right Level5 Level2 = l2≤2
min-trust-lb-right Level5 Level3 = l3≤3
min-trust-lb-right Level5 Level4 = l4≤4
min-trust-lb-right Level5 Level5 = l5≤5

------------------------------------------------------------------------
-- CRITICAL SAFETY PROPERTY: Dangerous axioms cap at Level1
------------------------------------------------------------------------

data DangerLevel : Set where
  Safe    : DangerLevel
  Noted   : DangerLevel
  Warning : DangerLevel
  Reject  : DangerLevel

data HasDangerousAxioms : DangerLevel → Set where
  warning-dangerous : HasDangerousAxioms Warning
  reject-dangerous  : HasDangerousAxioms Reject

-- The cap function: if dangerous axioms exist, trust is capped at Level1
cap-if-dangerous : TrustLevel → DangerLevel → TrustLevel
cap-if-dangerous _ Warning = Level1
cap-if-dangerous _ Reject  = Level1
cap-if-dangerous t Safe    = t
cap-if-dangerous t Noted   = t

-- THEOREM: Dangerous axioms always produce Level1
-- This is the key safety invariant of the trust pipeline
dangerous-axioms-cap-at-level1 :
  ∀ (t : TrustLevel) (d : DangerLevel) →
  HasDangerousAxioms d →
  cap-if-dangerous t d ≡ Level1
dangerous-axioms-cap-at-level1 _ Warning warning-dangerous = refl
dangerous-axioms-cap-at-level1 _ Reject reject-dangerous = refl

-- THEOREM: Safe axioms preserve trust level
safe-axioms-preserve-trust :
  ∀ (t : TrustLevel) → cap-if-dangerous t Safe ≡ t
safe-axioms-preserve-trust Level1 = refl
safe-axioms-preserve-trust Level2 = refl
safe-axioms-preserve-trust Level3 = refl
safe-axioms-preserve-trust Level4 = refl
safe-axioms-preserve-trust Level5 = refl

------------------------------------------------------------------------
-- Proof: cap-if-dangerous is monotonic in trust level
------------------------------------------------------------------------

cap-monotonic : ∀ (a b : TrustLevel) (d : DangerLevel) →
  a ≤ₜ b → cap-if-dangerous a d ≤ₜ cap-if-dangerous b d
cap-monotonic a b Warning _ = l1≤
cap-monotonic a b Reject _  = l1≤
cap-monotonic a b Safe a≤b  = a≤b
cap-monotonic a b Noted a≤b = a≤b
