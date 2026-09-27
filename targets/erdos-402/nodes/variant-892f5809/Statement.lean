import Mathlib
import Nodes.«variant-892f5809».Context

/-! Graham's gcd conjecture (Erdős problem 402) for 9-element sets: with M the largest element,
if every b had gcd(M, b) > M/9 then every other element would be (j/k)M with j < k < 9, and a
colouring of those values into 7 classes, each a set of pairwise "good" values, shows the
8 other elements cannot all avoid a pair x, y with 9 * gcd(x, y) ≤ max(x, y). -/

theorem Opn.erdos_402_card_nine :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 9 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
