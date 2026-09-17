import Mathlib

open scoped ArithmeticFunction.omega

theorem erdos_69__h1 : ∑' n : ℕ, (ω n : ℝ) / 2 ^ n
    = ∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1) := by
  sorry
