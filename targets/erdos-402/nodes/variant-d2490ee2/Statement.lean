import Mathlib
import Nodes.«variant-d2490ee2».Context

/-! Graham's gcd conjecture (Erdős problem 402) for seven-element sets. With M the largest
element, if gcd(M, b) > M/7 for every b then every other b is (j/k)M with j < k ≤ 6: one of
eleven values (in units of M/60: 10, 12, 15, 20, 24, 30, 36, 40, 45, 48, 50). Among those, no
six avoid a pair x, y with x / gcd(x, y) ≥ 7 (checked by a finite case split on which values
occur), so the six other elements cannot all be distinct values. -/

theorem Opn.erdos_402_card_seven :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 7 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
