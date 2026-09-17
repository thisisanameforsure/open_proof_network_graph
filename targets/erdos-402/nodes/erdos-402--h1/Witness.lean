import Mathlib

open Filter

theorem witness : ∃ (A : Finset ℕ) (m a b : ℕ), 0 ∉ A ∧ (∀ a ∈ A, ∀ b ∈ A, a ≤ m * a.gcd b) ∧ a ∈ A ∧ b ∈ A :=
  ⟨{1}, 1, 1, 1, by simp, by simp, by simp, by simp⟩
