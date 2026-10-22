-- relation: partial
import Mathlib

/-! The variant is a partial form of the root (D-30, `partial`): the root, for every infinite
set, specialises to the sets with arbitrarily long gaps. -/

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    (∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
      (∀ C : ℕ, ∃ m ∈ A, ∃ F : Finset ℕ, (∀ a, a ∈ F ↔ a ∈ A ∧ a < m) ∧ C + ∑ a ∈ F, a ≤ m) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) := by
  intro h A hA _ _
  exact h A hA
