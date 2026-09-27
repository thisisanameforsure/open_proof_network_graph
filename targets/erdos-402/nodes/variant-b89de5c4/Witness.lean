import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 18 :=
  ⟨Finset.Icc 1 18, by simp, by simp⟩
