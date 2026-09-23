import Mathlib
import Nodes.«variant-950630b9».Context

/-! Graham's gcd conjecture (Erdős problem 402) when the largest element of `A` is coprime
to some element of `A`: then that pair has gcd 1, and `|A| ≤ max A` because `A` is a set of
positive integers at most `max A`. -/

theorem Opn.erdos_402_max_coprime :
    ∀ (A : Finset ℕ), 0 ∉ A → (∃ m ∈ A, ∃ b ∈ A, (∀ c ∈ A, c ≤ m) ∧ m.Coprime b) →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
