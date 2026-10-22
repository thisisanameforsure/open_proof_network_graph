-- relation: partial
import Mathlib

/-! The variant is a partial form of the root (D-30, `partial`): the root, applied to the
infinite union of the powers of two bases. -/

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    ∀ a b : ℕ, 2 ≤ a → a < b →
    Irrational (∑' n : ({n | ∃ k : ℕ, n = a ^ k} ∪ {n | ∃ k : ℕ, n = b ^ k} : Set ℕ),
      (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro h a b ha _
  apply h
  apply Set.Infinite.mono Set.subset_union_left
  have : {n | ∃ k : ℕ, n = a ^ k} = Set.range (fun k : ℕ => a ^ k) := by
    ext n; simp [eq_comm]
  rw [this]
  exact Set.infinite_range_of_injective (Nat.pow_right_injective ha)
