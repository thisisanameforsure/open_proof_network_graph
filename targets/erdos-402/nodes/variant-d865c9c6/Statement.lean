import Mathlib
import Nodes.«variant-d865c9c6».Context

/-! Graham's gcd conjecture (Erdős problem 402) for two-element sets: the larger element's
gcd with the smaller is a proper divisor of it, so it is at most half of it. -/

theorem Opn.erdos_402_card_two :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 2 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
