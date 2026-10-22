-- relation: partial
import Mathlib

/-! The variant is a partial form of the root (D-30, `partial`): the root, applied to the
infinite union of two fast divisibility chains. -/

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    ∀ x y : ℕ → ℕ, 0 < x 0 → 0 < y 0 →
    (∀ j, x j ∣ x (j + 1)) → (∀ j, y j ∣ y (j + 1)) →
    (∀ j, 3 * x j ≤ x (j + 1)) → (∀ j, 3 * y j ≤ y (j + 1)) →
    Irrational (∑' n : (Set.range x ∪ Set.range y : Set ℕ), (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro h x y hx0 _ _ _ hx3 _
  apply h
  apply Set.Infinite.mono Set.subset_union_left
  apply Set.infinite_range_of_injective
  have hgt : ∀ j, j < x j := by
    intro j
    induction j with
    | zero => exact hx0
    | succ j ih => have := hx3 j; omega
  apply StrictMono.injective
  apply strictMono_nat_of_lt_succ
  intro j
  have := hx3 j; have := hgt j; omega
