-- SPDX-License-Identifier: PMPL-1.0-or-later
-- IdentityLaws.agda — trivial proofs that compile cleanly against
-- agda-stdlib v2.3. Exists to exercise the echidnabot agda runner
-- with a known-good file alongside the pre-existing (broken) corpus.

module IdentityLaws where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Addition has zero as left identity, by definition.
+-left-id : (n : ℕ) → zero + n ≡ n
+-left-id _ = refl

-- Zero as right identity needs induction on n.
+-right-id : (n : ℕ) → n + zero ≡ n
+-right-id zero    = refl
+-right-id (suc n) = cong suc (+-right-id n)
