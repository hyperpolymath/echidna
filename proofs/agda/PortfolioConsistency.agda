-- SPDX-License-Identifier: PMPL-1.0-or-later
-- PortfolioConsistency.agda — All-true implies Any-true for non-empty Vec Bool.
--
-- Models an ECHIDNA portfolio of n independent prover results as a
-- Vec Bool n.  Proves:
--   1. If All elements of a non-empty vector satisfy IsTrue (every prover
--      succeeded), then Any element satisfies IsTrue (at least one succeeded).
--   2. Contrapositive: ¬ Any → ¬ All for non-empty vectors.
--
-- This formalises the soundness invariant: an empty portfolio verdict
-- can never masquerade as a universal pass.

module PortfolioConsistency where

open import Data.Bool  using (Bool; true; false)
open import Data.Nat   using (ℕ; zero; suc)
open import Data.Vec   using (Vec; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec.Relation.Unary.All using (All)
  renaming ([] to All[]; _∷_ to _All∷_)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)

------------------------------------------------------------------------
-- 1.  Unit type (needed before IsTrue)
------------------------------------------------------------------------

record ⊤ : Set where
  constructor tt

------------------------------------------------------------------------
-- 2.  Predicate: IsTrue b holds iff b is true
------------------------------------------------------------------------

IsTrue : Bool → Set
IsTrue true  = ⊤
IsTrue false = ⊥

------------------------------------------------------------------------
-- 3.  Main theorem: All IsTrue xs → Any IsTrue xs (non-empty xs)
------------------------------------------------------------------------

-- For any *non-empty* vector where every element satisfies IsTrue,
-- at least one element satisfies IsTrue.
-- Proof: the head is true (by All), so `here` witnesses Any.
All→Any : {n : ℕ} {xs : Vec Bool (suc n)}
        → All IsTrue xs
        → Any IsTrue xs
All→Any (px All∷ _) = here px

------------------------------------------------------------------------
-- 4.  Contrapositive: ¬ Any IsTrue xs → ¬ All IsTrue xs
------------------------------------------------------------------------

-- Direct: if no element is true, then we cannot have all elements true,
-- since All→Any would then produce a witness for Any, contradicting ¬ Any.
¬any→¬all : {n : ℕ} {xs : Vec Bool (suc n)}
           → ¬ Any IsTrue xs
           → ¬ All IsTrue xs
¬any→¬all ¬any allP = ¬any (All→Any allP)

------------------------------------------------------------------------
-- 5.  Sanity checks: unit vectors
------------------------------------------------------------------------

-- [true] satisfies All IsTrue.
unit-all : All IsTrue (true ∷ [])
unit-all = tt All∷ All[]

-- [true] satisfies Any IsTrue (via the theorem above).
unit-any : Any IsTrue (true ∷ [])
unit-any = All→Any unit-all

-- [false] satisfies neither All nor Any.
¬all-false : ¬ All IsTrue (false ∷ [])
¬all-false (bot All∷ _) = ⊥-elim bot

¬any-false : ¬ Any IsTrue (false ∷ [])
¬any-false (here  bot) = ⊥-elim bot
¬any-false (there imp) = ¬any-false-nil imp
  where
    ¬any-false-nil : ¬ Any IsTrue ([] {A = Bool})
    ¬any-false-nil ()

------------------------------------------------------------------------
-- 6.  Extension lemma: if the head is true the extended vector has Any
------------------------------------------------------------------------

-- If the first result in the portfolio is a success, the whole portfolio
-- has at least one success — regardless of the tail.
head-true→any : {n : ℕ} {xs : Vec Bool n}
              → Any IsTrue (true ∷ xs)
head-true→any = here tt
