import Mathlib
import Nodes.«variant-bc28297c».Context

/-! Graham's gcd conjecture (Erdős problem 402) for five-element sets: with M the largest
element, if every b had gcd(M, b) > M/5 then every b would be (j/k)M with j ≤ k ≤ 4, and any
five of those six values contain a pair 9s, 8s or 8s, 3s or 9s, 4s whose gcd is s. -/

theorem Opn.erdos_402_card_five :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 5 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
