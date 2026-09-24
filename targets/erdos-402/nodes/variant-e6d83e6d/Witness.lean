import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 6 :=
  ⟨{1, 2, 3, 4, 5, 6}, by decide, by decide⟩
