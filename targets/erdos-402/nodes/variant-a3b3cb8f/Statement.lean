import Mathlib
import Nodes.«variant-a3b3cb8f».Context

/-! Graham's gcd conjecture (Erdős problem 402) for 7-element sets: with M the largest element,
if every b had gcd(M, b) > M/7 then every other element would be (j/k)M with j < k < 7, and a
finite check shows any 6 of those values contain a pair whose gcd is at most the larger over 7. -/

theorem Opn.erdos_402_card_seven :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 7 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
