import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 10 := ⟨Finset.Icc 1 10, by decide, by decide⟩
