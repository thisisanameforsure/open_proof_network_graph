import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 2 :=
  ⟨{1, 2}, by decide, by decide⟩
