-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Nat.agda — natural number arithmetic proofs over agda-stdlib.

module Nat where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- Left-identity of addition: definitionally true, no induction needed.
+-left-id : (n : ℕ) → zero + n ≡ n
+-left-id _ = refl

-- Right-identity of addition: requires induction on n.
+-right-id : (n : ℕ) → n + zero ≡ n
+-right-id zero    = refl
+-right-id (suc n) = cong suc (+-right-id n)

-- Successor shifts through addition.
+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero    _ = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- Addition commutes.
+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero    n = sym (+-right-id n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

-- Zero absorbs multiplication on the left (definitional).
*-left-zero : (n : ℕ) → zero * n ≡ zero
*-left-zero _ = refl
