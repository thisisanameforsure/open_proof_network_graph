import Mathlib
import Nodes.«variant-780e7ade».Context

/-! Graham's gcd conjecture (Erdős problem 402) for four-element sets: with M the largest
element, if every b had gcd(M, b) > M/4 then every b would be one of M, M/2, M/3, 2M/3, and
the pair 2M/3, M/2 = 4t, 3t has gcd t, which is a quarter of 4t. -/

theorem Opn.erdos_402_card_four :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 4 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
