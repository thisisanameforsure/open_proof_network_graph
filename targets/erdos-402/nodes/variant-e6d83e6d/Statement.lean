import Mathlib
import Nodes.«variant-e6d83e6d».Context

/-! Graham's gcd conjecture (Erdős problem 402) for 6-element sets: with M the largest element,
if every b had gcd(M, b) > M/6 then every other element would be (j/k)M with j < k < 6, and a
finite check shows any 5 of those values contain a pair whose gcd is at most the larger over 6. -/

theorem Opn.erdos_402_card_six :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 6 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
