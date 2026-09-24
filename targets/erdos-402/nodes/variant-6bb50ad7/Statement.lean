import Mathlib
import Nodes.«variant-6bb50ad7».Context

/-! Graham's gcd conjecture (Erdős problem 402) for eight-element sets. With M the largest
element, if gcd(M, b) > M/8 for every b then every other b is (j/k)M with j < k ≤ 7: one of
seventeen values. Among those, no seven avoid a pair x, y with x / gcd(x, y) ≥ 8 (a finite
case split on which values occur), so the seven other elements cannot all be distinct values. -/

theorem Opn.erdos_402_card_eight :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 8 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
