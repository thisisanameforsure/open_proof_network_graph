import Mathlib

theorem witness : ∃ (A : Finset ℕ) (p : ℕ), 0 ∉ A ∧ p ∈ A ∧ p.Prime ∧ A.card ≤ p :=
  ⟨{2}, 2, by decide, by simp, Nat.prime_two, by simp⟩
