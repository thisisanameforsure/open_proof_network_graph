import Mathlib

theorem witness : ∃ (A : Finset ℕ), 0 ∉ A ∧ ∃ m ∈ A, ∃ b ∈ A, (∀ c ∈ A, c ≤ m) ∧ m.Coprime b :=
  ⟨{1}, by decide, 1, by simp, 1, by simp, by simp, by norm_num⟩
