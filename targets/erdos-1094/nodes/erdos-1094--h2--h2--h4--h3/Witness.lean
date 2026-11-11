import Mathlib

open scoped Nat

theorem witness : ∃ η : ℝ, (0 : ℝ) < η := ⟨1, one_pos⟩
