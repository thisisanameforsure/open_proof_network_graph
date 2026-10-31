-- relation: refutes
import Mathlib

/-! The variant refutes the root (D-30, `refutes`): an infinite set whose Mersenne reciprocal
sum is a rational number is a witness against "every infinite set's sum is irrational". -/

theorem relation :
    (∃ A : Set ℕ, A.Infinite ∧ ∃ s : ℚ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = s) →
    ¬ (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) := by
  rintro ⟨A, hA, s, hs⟩ h
  exact h A hA ⟨s, hs.symm⟩
