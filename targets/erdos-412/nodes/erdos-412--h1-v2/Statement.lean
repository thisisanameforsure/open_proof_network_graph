import Mathlib

open ArithmeticFunction.sigma

theorem erdos_412__h1 : ∀ m, 3 ≤ m → (¬ ∃ x, 2 ≤ x ∧ x < m ∧ ∃ k, (σ 1)^[k] x = m) →
    ∃ m', 2 ≤ m' ∧ m' < m ∧ ∃ i j, (σ 1)^[i] m = (σ 1)^[j] m' := by
  sorry
