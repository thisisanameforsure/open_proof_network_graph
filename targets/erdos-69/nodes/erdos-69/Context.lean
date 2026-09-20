import Mathlib

/-! Declared dependencies (D-4 step 8): `erdos-69--h1-v2`, `erdos-69--h2-v2`. -/

open scoped ArithmeticFunction.omega

theorem erdos_69__h1 : ∑' n : ℕ, (ω n : ℝ) / 2 ^ n
    = ∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1) := by
  sorry


open scoped ArithmeticFunction.omega

theorem erdos_69__h2 : (∑' n : ℕ, (ω n : ℝ) / 2 ^ n
      = ∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1)) →
    Irrational (∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1)) := by
  sorry
