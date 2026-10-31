import Mathlib

theorem witness : ∃ (x : ℚ) (r : ℕ → ℝ) (q : ℕ → ℕ), 0 ≤ x ∧ r 0 = x ∧
    (∀ m : ℕ, q m = ⌊r m / ((1 : ℝ) / (2 ^ m - 1))⌋₊ ∧
            r (m + 1) = r m - q m * ((1 : ℝ) / (2 ^ m - 1))) ∧
    ∑' n : {m : ℕ | q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1)},
              (1 : ℝ) / (2 ^ n.1 - 1) =
      x - ∑' m : ℕ, ((q m : ℝ) -
              if q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1) then 1 else 0) *
                ((1 : ℝ) / (2 ^ m - 1)) ∧
    {m : ℕ | ((q m : ℝ) -
              if q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1) then 1 else 0) ≠ 0}.Finite := by
  refine ⟨0, fun _ => 0, fun _ => 0, le_rfl, by simp, fun m => by simp, ?_, ?_⟩
  · simp
  · simp
