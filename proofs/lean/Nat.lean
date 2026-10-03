/-
SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: MPL-2.0

Natural Number Proofs in Lean 4

This file demonstrates proofs about natural numbers:
- Basic arithmetic properties
- Induction principles
- Simple number theory
- Ordering properties

These serve as test cases for ECHIDNA's Lean backend integration.
-/

namespace ECHIDNA.Nat

/-! ## Basic Arithmetic Properties -/

/--
Zero is the additive identity (right).
-/
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

/--
Zero is the additive identity (left).
-/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]

/--
One is the multiplicative identity (right).
-/
theorem mul_one (n : Nat) : n * 1 = n :=
  _root_.Nat.mul_one n

/--
One is the multiplicative identity (left).
-/
theorem one_mul (n : Nat) : 1 * n = n :=
  _root_.Nat.one_mul n

/--
Zero is the multiplicative annihilator (right).
-/
theorem mul_zero (n : Nat) : n * 0 = 0 :=
  _root_.Nat.mul_zero n

/--
Zero is the multiplicative annihilator (left).
-/
theorem zero_mul (n : Nat) : 0 * n = 0 :=
  _root_.Nat.zero_mul n


/-! ## Commutativity -/

/--
Addition is commutative.
-/
theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero =>
    rw [_root_.Nat.add_zero, zero_add]
  | succ n ih =>
    rw [_root_.Nat.add_succ, _root_.Nat.succ_add, ih]

/--
Multiplication is commutative.
-/
theorem mul_comm (m n : Nat) : m * n = n * m :=
  _root_.Nat.mul_comm m n


/-! ## Associativity -/

/--
Addition is associative.
-/
theorem add_assoc (m n k : Nat) : (m + n) + k = m + (n + k) := by
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    rw [_root_.Nat.add_succ, _root_.Nat.add_succ, _root_.Nat.add_succ, ih]

/--
Multiplication is associative.
-/
theorem mul_assoc (m n k : Nat) : (m * n) * k = m * (n * k) :=
  _root_.Nat.mul_assoc m n k


/-! ## Distributivity -/

/--
Left distributivity: m * (n + k) = m * n + m * k
-/
theorem left_distrib (m n k : Nat) : m * (n + k) = m * n + m * k :=
  _root_.Nat.left_distrib m n k

/--
Right distributivity: (m + n) * k = m * k + n * k
-/
theorem right_distrib (m n k : Nat) : (m + n) * k = m * k + n * k :=
  _root_.Nat.right_distrib m n k


/-! ## Induction Examples -/

/--
Sum of first n natural numbers (Gauss formula).
We define our own sum function to avoid Mathlib dependency.
-/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo]
    rw [_root_.Nat.mul_add, ih, ← _root_.Nat.add_mul, _root_.Nat.mul_comm (2 + n)]
    congr 1
    omega

/--
Simple induction: n + n = 2 * n
-/
theorem double_add (n : Nat) : n + n = 2 * n := by omega

/--
Power of 2 grows: 2^n ≥ n for all n ≥ 1
-/
theorem pow2_ge (n : Nat) : n ≥ 1 → 2^n ≥ n := by
  intro h
  induction n with
  | zero =>
    cases h
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have : n + 1 ≥ 1 := _root_.Nat.succ_le_succ (_root_.Nat.zero_le n)
      have prev := ih this
      simp [Nat.pow_succ]
      omega


/-! ## Comparison and Ordering -/

/--
Reflexivity of ≤.
-/
theorem le_refl (n : Nat) : n ≤ n :=
  _root_.Nat.le_refl n

/--
Antisymmetry of ≤.
-/
theorem le_antisymm (m n : Nat) : m ≤ n → n ≤ m → m = n :=
  fun h1 h2 => _root_.Nat.le_antisymm h1 h2

/--
Transitivity of ≤.
-/
theorem le_trans (m n k : Nat) : m ≤ n → n ≤ k → m ≤ k :=
  fun h1 h2 => _root_.Nat.le_trans h1 h2

/--
Successor is greater.
-/
theorem lt_succ_self (n : Nat) : n < n + 1 :=
  _root_.Nat.lt_succ_self n

/--
Zero is the minimum natural number.
-/
theorem zero_le (n : Nat) : 0 ≤ n :=
  _root_.Nat.zero_le n


/-! ## Addition Properties -/

/--
Left cancellation for addition: k + m = k + n → m = n
-/
theorem add_left_cancel (k m n : Nat) : k + m = k + n → m = n :=
  _root_.Nat.add_left_cancel

/--
Right cancellation for addition: m + k = n + k → m = n
-/
theorem add_right_cancel (k m n : Nat) : m + k = n + k → m = n :=
  fun h => _root_.Nat.add_right_cancel h

/--
Addition preserves ordering (left).
-/
theorem add_le_add_left (m n k : Nat) : m ≤ n → k + m ≤ k + n :=
  fun h => _root_.Nat.add_le_add_left h k

/--
Addition preserves ordering (right).
-/
theorem add_le_add_right (m n k : Nat) : m ≤ n → m + k ≤ n + k :=
  fun h => _root_.Nat.add_le_add_right h k


/-! ## Multiplication Properties -/

/--
Multiplication by successor: m * (n + 1) = m * n + m
-/
theorem mul_succ (m n : Nat) : m * (n + 1) = m * n + m :=
  _root_.Nat.mul_succ m n

/--
Successor times: (m + 1) * n = m * n + n
-/
theorem succ_mul (m n : Nat) : (m + 1) * n = m * n + n :=
  _root_.Nat.succ_mul m n

/--
Left cancellation for multiplication (when k > 0).
-/
theorem mul_left_cancel (k m n : Nat) : k > 0 → k * m = k * n → m = n := by
  intro hk h
  cases k with
  | zero => cases hk
  | succ k =>
    exact _root_.Nat.eq_of_mul_eq_mul_left (_root_.Nat.zero_lt_succ k) h


/-! ## Subtraction Properties -/

/--
Subtraction of zero.
-/
theorem sub_zero (n : Nat) : n - 0 = n := by
  rfl

/--
Self subtraction.
-/
theorem sub_self (n : Nat) : n - n = 0 :=
  _root_.Nat.sub_self n

/--
Subtraction and addition (when n ≤ m).
-/
theorem sub_add_cancel (m n : Nat) : n ≤ m → (m - n) + n = m :=
  _root_.Nat.sub_add_cancel


/-! ## Simple Number Theory -/

/--
Even number definition: n is even if n = 2k for some k.
-/
def is_even (n : Nat) : Prop := ∃ k, n = 2 * k

/--
Odd number definition: n is odd if n = 2k + 1 for some k.
-/
def is_odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/--
Zero is even.
-/
theorem zero_is_even : is_even 0 := ⟨0, rfl⟩

/--
One is odd.
-/
theorem one_is_odd : is_odd 1 := ⟨0, rfl⟩

/--
Two is even.
-/
theorem two_is_even : is_even 2 := ⟨1, rfl⟩

/--
Sum of two even numbers is even.
-/
theorem even_add_even (m n : Nat) : is_even m → is_even n → is_even (m + n) := by
  intro ⟨k, hm⟩ ⟨j, hn⟩
  exact ⟨k + j, by rw [hm, hn]; omega⟩

/--
Product of any number with an even number is even.
-/
theorem mul_even (m n : Nat) : is_even n → is_even (m * n) := by
  intro ⟨k, hn⟩
  exact ⟨m * k, by
    rw [hn]
    rw [← _root_.Nat.mul_assoc, _root_.Nat.mul_comm m 2, _root_.Nat.mul_assoc]⟩


/-! ## Division Properties -/

/--
Division by 1 is identity.
-/
theorem div_one (n : Nat) : n / 1 = n :=
  _root_.Nat.div_one n

/--
Self division (when n > 0).
-/
theorem div_self (n : Nat) : n > 0 → n / n = 1 :=
  fun _ => _root_.Nat.div_self ‹_›


/-! ## Modulo Properties -/

/--
Modulo 1 is always 0.
-/
theorem mod_one (n : Nat) : n % 1 = 0 :=
  _root_.Nat.mod_one n

/--
Modulo self (when n > 0).
-/
theorem mod_self (n : Nat) : n > 0 → n % n = 0 :=
  fun _ => _root_.Nat.mod_self n

/--
Modulo is less than divisor (when divisor > 0).
-/
theorem mod_lt (m n : Nat) : n > 0 → m % n < n :=
  _root_.Nat.mod_lt m


/-! ## GCD Properties -/

/--
GCD is commutative.
-/
theorem gcd_comm (m n : Nat) : Nat.gcd m n = Nat.gcd n m :=
  _root_.Nat.gcd_comm m n

/--
GCD with zero.
-/
theorem gcd_zero_right (n : Nat) : Nat.gcd n 0 = n :=
  _root_.Nat.gcd_zero_right n

/--
GCD with self.
-/
theorem gcd_self (n : Nat) : Nat.gcd n n = n :=
  _root_.Nat.gcd_self n


end ECHIDNA.Nat
