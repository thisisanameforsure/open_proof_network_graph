import Mathlib
import Nodes.«variant-a5969ff3».Context

/-! Graham's gcd conjecture (Erdős problem 402) for 10-element sets: with M the largest element,
if every b had gcd(M, b) > M/10 then every other element would be (j/k)M with j < k < 10, and a
colouring of those values into 8 classes, each a set of pairwise "good" values, shows the
9 other elements cannot all avoid a pair x, y with 10 * gcd(x, y) ≤ max(x, y). -/

theorem Opn.erdos_402_card_ten :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 10 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
