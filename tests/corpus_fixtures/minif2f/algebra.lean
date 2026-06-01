import Mathlib.Tactic

theorem mathd_algebra_42 (x : ℝ) (h : x + 1 = 2) : x = 1 := by
  linarith

theorem mathd_algebra_171 (a b : ℝ) (h₀ : a + b = 10) (h₁ : a - b = 4) : a = 7 := by
  linarith

theorem imo_1959_p1 (n : ℕ) (h : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  sorry
