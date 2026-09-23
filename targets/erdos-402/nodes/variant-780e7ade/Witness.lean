import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 4 :=
  ⟨{1, 2, 3, 4}, by decide, by decide⟩
