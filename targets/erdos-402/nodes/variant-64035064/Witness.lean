import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 16 :=
  ⟨Finset.Icc 1 16, by simp, by simp⟩
