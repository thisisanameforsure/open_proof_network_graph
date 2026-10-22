-- relation: partial
import Mathlib

/-! The variant is a partial form of the root (D-30, `partial`): the root, for every infinite
set, specialises to the sets meeting Liouville's criterion. -/

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    (∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
      (∀ C : ℕ, ∃ m ∈ A, ∃ L : ℕ, 0 < L ∧ (∀ a ∈ A, a < m → 2 ^ a - 1 ∣ L) ∧ 2 ^ C * L ≤ 2 ^ m) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) := by
  intro h A hA _ _
  exact h A hA
