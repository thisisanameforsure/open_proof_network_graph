import Mathlib

theorem witness : ∃ (x : ℕ → ℕ) (y : ℕ → ℕ), 0 < x 0 ∧ 0 < y 0 ∧
    (∀ j, x j ∣ x (j + 1)) ∧ (∀ j, y j ∣ y (j + 1)) ∧
    (∀ j, 3 * x j ≤ x (j + 1)) ∧ (∀ j, 3 * y j ≤ y (j + 1)) := by
  refine ⟨fun j => 3 ^ j, fun j => 4 ^ j, by positivity, by positivity,
    fun j => pow_dvd_pow 3 (Nat.le_succ j), fun j => pow_dvd_pow 4 (Nat.le_succ j), ?_, ?_⟩
  · intro j; show 3 * 3 ^ j ≤ 3 ^ (j + 1); rw [pow_succ]; omega
  · intro j; show 3 * 4 ^ j ≤ 4 ^ (j + 1); rw [pow_succ]; omega
