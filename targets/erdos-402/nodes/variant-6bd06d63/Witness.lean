import Mathlib

theorem witness : ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = 3 :=
  ⟨{1, 2, 3}, by decide, by decide⟩
