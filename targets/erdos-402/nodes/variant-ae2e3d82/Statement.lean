import Mathlib
import Nodes.«variant-ae2e3d82».Context

/-! Graham's gcd conjecture (Erdős problem 402) for six-element sets. With M the largest
element, if gcd(M, b) > M/6 for every b then every other b is (j/k)M with j < k ≤ 5: one of the
nine values 30s, 20s, 40s, 15s, 45s, 12s, 24s, 36s, 48s (s = M/60). Any five of those nine
contain a pair x, y with x / gcd(x, y) ≥ 6 (e.g. 48s and 30s, 36s and 20s, 40s and 12s), so the
five other elements cannot all be distinct values. -/

theorem Opn.erdos_402_card_six :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 6 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
