-- relation: partial
import Mathlib

/-! The variant is a partial form of the root (D-30, `partial`): the root, applied to the
infinite set of powers of two and of three. -/

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    Irrational (∑' n : ({n | ∃ k : ℕ, n = 2 ^ k} ∪ {n | ∃ k : ℕ, n = 3 ^ k} : Set ℕ),
      (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro h
  apply h
  apply Set.Infinite.mono Set.subset_union_left
  have : {n | ∃ k : ℕ, n = 2 ^ k} = Set.range (fun k : ℕ => 2 ^ k) := by
    ext n; simp [eq_comm]
  rw [this]
  exact Set.infinite_range_of_injective (Nat.pow_right_injective (le_refl 2))
