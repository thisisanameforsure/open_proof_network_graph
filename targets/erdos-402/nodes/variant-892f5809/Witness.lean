import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 9 := ⟨Finset.Icc 1 9, by decide, by decide⟩
