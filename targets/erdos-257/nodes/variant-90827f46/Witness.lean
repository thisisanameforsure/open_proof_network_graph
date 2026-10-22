import Mathlib

theorem witness : ∃ (r : ℕ) (c : Fin r → ℕ → ℕ), 0 < r ∧ (∀ i, 0 < c i 0) ∧
    ∀ i j, (2 * r + 1) ^ (r + 1) * c i j ≤ c i (j + 1) := by
  refine ⟨1, fun _ j => 9 ^ j, by norm_num, fun _ => by positivity, ?_⟩
  intro _ j
  show (2 * 1 + 1) ^ (1 + 1) * 9 ^ j ≤ 9 ^ (j + 1)
  rw [pow_succ]
  omega
