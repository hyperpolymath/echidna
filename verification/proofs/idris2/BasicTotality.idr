-- SPDX-License-Identifier: PMPL-1.0-or-later
-- BasicTotality.idr — small, correct totality proofs that compile
-- cleanly under `idris2 --source-dir . --check`. Exists to populate
-- the totality obligation_class alongside DispatchCorrectness.idr
-- while the larger generated proofs (AxiomCompleteness, DispatchOrdering,
-- ProverKindInjectivity) are being repaired.

module BasicTotality

%default total

-- Structural recursion on Nat is automatically total.
double : Nat -> Nat
double Z     = Z
double (S n) = S (S (double n))

-- Length of a List by structural recursion.
lengthL : List a -> Nat
lengthL []        = Z
lengthL (_ :: xs) = S (lengthL xs)

-- Append preserves length additively.
lenAppend : (xs, ys : List a) -> lengthL (xs ++ ys) = lengthL xs + lengthL ys
lenAppend []        ys = Refl
lenAppend (x :: xs) ys = cong S (lenAppend xs ys)

-- Map preserves length.
mapLen : (f : a -> b) -> (xs : List a) -> lengthL (map f xs) = lengthL xs
mapLen f []        = Refl
mapLen f (x :: xs) = cong S (mapLen f xs)

-- Double of sum equals sum of doubles — a simple arithmetic law.
doubleAdd : (m, n : Nat) -> double (m + n) = double m + double n
doubleAdd Z     _ = Refl
doubleAdd (S m) n = cong (S . S) (doubleAdd m n)
