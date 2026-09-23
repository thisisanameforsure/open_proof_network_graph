import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 5 :=
  ⟨{1, 2, 3, 4, 5}, by decide, by decide⟩
