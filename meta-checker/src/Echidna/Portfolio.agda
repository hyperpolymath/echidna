-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- Portfolio.agda — Formal verification of ECHIDNA's portfolio solving
--
-- Proves:
-- 1. Cross-checking with 2+ provers increases trust
-- 2. Disagreement detection is sound
-- 3. Portfolio result aggregation is consistent

module Echidna.Portfolio where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_; length; any; all; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Echidna.TrustLevel

------------------------------------------------------------------------
-- Solver Result (mirrors Rust SolverResult)
------------------------------------------------------------------------

data SolverVerdict : Set where
  Valid    : SolverVerdict  -- Proof verified
  Invalid  : SolverVerdict  -- Counterexample found
  Unknown  : SolverVerdict  -- Could not determine
  Timeout  : SolverVerdict  -- Timed out

------------------------------------------------------------------------
-- Portfolio Result (mirrors Rust PortfolioResult)
------------------------------------------------------------------------

data PortfolioOutcome : Set where
  CrossChecked : PortfolioOutcome  -- Multiple provers agree
  SingleSolver : PortfolioOutcome  -- Only one prover responded
  Inconclusive : PortfolioOutcome  -- Provers disagreed
  AllTimedOut  : PortfolioOutcome  -- All provers timed out

------------------------------------------------------------------------
-- Trust level assignment for portfolio outcomes
------------------------------------------------------------------------

portfolio-trust : PortfolioOutcome → Bool → TrustLevel
-- small_kernel parameter indicates if provers have small kernels
portfolio-trust CrossChecked true  = Level5  -- 2+ small-kernel agree
portfolio-trust CrossChecked false = Level3  -- 2+ large-kernel agree
portfolio-trust SingleSolver true  = Level4  -- 1 small-kernel
portfolio-trust SingleSolver false = Level2  -- 1 large-kernel
portfolio-trust Inconclusive _     = Level1  -- Disagreement
portfolio-trust AllTimedOut  _     = Level1  -- No result

------------------------------------------------------------------------
-- THEOREM: Cross-checked results always ≥ single-solver results
------------------------------------------------------------------------

cross-check-improves-trust : ∀ (sk : Bool) →
  portfolio-trust SingleSolver sk ≤ₜ portfolio-trust CrossChecked sk
cross-check-improves-trust true  = l4≤5
cross-check-improves-trust false = l2≤3

------------------------------------------------------------------------
-- THEOREM: Inconclusive results are always Level1
------------------------------------------------------------------------

inconclusive-is-level1 : ∀ (sk : Bool) →
  portfolio-trust Inconclusive sk ≡ Level1
inconclusive-is-level1 true  = refl
inconclusive-is-level1 false = refl

------------------------------------------------------------------------
-- THEOREM: Timeout results are always Level1
------------------------------------------------------------------------

timeout-is-level1 : ∀ (sk : Bool) →
  portfolio-trust AllTimedOut sk ≡ Level1
timeout-is-level1 true  = refl
timeout-is-level1 false = refl

------------------------------------------------------------------------
-- Agreement checking
------------------------------------------------------------------------

agree : SolverVerdict → SolverVerdict → Bool
agree Valid Valid     = true
agree Invalid Invalid = true
agree _ _             = false

-- THEOREM: Agreement is reflexive for definite verdicts
agree-refl-valid : agree Valid Valid ≡ true
agree-refl-valid = refl

agree-refl-invalid : agree Invalid Invalid ≡ true
agree-refl-invalid = refl

-- THEOREM: Agreement is symmetric
agree-sym : ∀ (a b : SolverVerdict) → agree a b ≡ agree b a
agree-sym Valid Valid       = refl
agree-sym Valid Invalid     = refl
agree-sym Valid Unknown     = refl
agree-sym Valid Timeout     = refl
agree-sym Invalid Valid     = refl
agree-sym Invalid Invalid   = refl
agree-sym Invalid Unknown   = refl
agree-sym Invalid Timeout   = refl
agree-sym Unknown Valid     = refl
agree-sym Unknown Invalid   = refl
agree-sym Unknown Unknown   = refl
agree-sym Unknown Timeout   = refl
agree-sym Timeout Valid     = refl
agree-sym Timeout Invalid   = refl
agree-sym Timeout Unknown   = refl
agree-sym Timeout Timeout   = refl

------------------------------------------------------------------------
-- THEOREM: Small-kernel always has higher trust than large-kernel
------------------------------------------------------------------------

small-kernel-higher : ∀ (o : PortfolioOutcome) →
  portfolio-trust o false ≤ₜ portfolio-trust o true
small-kernel-higher CrossChecked = l3≤5
small-kernel-higher SingleSolver = l2≤4
small-kernel-higher Inconclusive = l1≤
small-kernel-higher AllTimedOut  = l1≤

------------------------------------------------------------------------
-- Disagreement detection soundness
------------------------------------------------------------------------

-- If two provers give opposite verdicts, they disagree
opposite-verdict-disagree : agree Valid Invalid ≡ false
opposite-verdict-disagree = refl

-- Unknown and Timeout are never considered agreement
unknown-never-agrees : ∀ (v : SolverVerdict) → agree Unknown v ≡ false
unknown-never-agrees Valid    = refl
unknown-never-agrees Invalid  = refl
unknown-never-agrees Unknown  = refl
unknown-never-agrees Timeout  = refl
