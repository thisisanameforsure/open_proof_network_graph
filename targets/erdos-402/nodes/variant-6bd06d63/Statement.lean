import Mathlib
import Nodes.«variant-6bd06d63».Context

/-! Graham's gcd conjecture (Erdős problem 402) for three-element sets: with M the largest
element, if every b had gcd(M, b) > M/3 then every b would be M or M/2, so A has at most two
elements. -/

theorem Opn.erdos_402_card_three :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 3 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
