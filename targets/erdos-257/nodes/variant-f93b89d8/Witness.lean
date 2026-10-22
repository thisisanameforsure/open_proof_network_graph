import Mathlib

theorem witness : ∃ (a : ℕ) (b : ℕ), (2 : ℕ) ≤ a ∧ a < b := ⟨2, 3, le_refl 2, by norm_num⟩
