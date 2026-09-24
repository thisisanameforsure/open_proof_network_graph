import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 8 :=
  ⟨{1, 2, 3, 4, 5, 6, 7, 8}, by decide, by decide⟩
