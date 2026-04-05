-- SPDX-License-Identifier: PMPL-1.0-or-later
-- List.agda — list-manipulation proofs over agda-stdlib.

module List where

open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Append has nil as left identity (definitional).
++-left-id : {A : Set} → (xs : List A) → [] ++ xs ≡ xs
++-left-id _ = refl

-- Append has nil as right identity (induction).
++-right-id : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
++-right-id []       = refl
++-right-id (x ∷ xs) = cong (x ∷_) (++-right-id xs)

-- Append is associative.
++-assoc : {A : Set} → (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       _  _  = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

-- Length distributes over append.
length-++ : {A : Set} → (xs ys : List A)
          → length (xs ++ ys) ≡ length xs + length ys
length-++ []       _  = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)
