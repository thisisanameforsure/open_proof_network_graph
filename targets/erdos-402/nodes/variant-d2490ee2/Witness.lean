import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 7 :=
  ⟨{1, 2, 3, 4, 5, 7}, by decide, by decide⟩
