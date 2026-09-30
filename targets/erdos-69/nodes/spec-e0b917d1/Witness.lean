import Mathlib

theorem witness : ∃ P j : ℕ, 2 ≤ P ∧ j ≤ P := ⟨2, 0, le_rfl, Nat.zero_le _⟩
