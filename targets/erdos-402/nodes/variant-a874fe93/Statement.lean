import Mathlib
import Nodes.«variant-a874fe93».Context

/-! Graham's gcd conjecture (Erdős problem 402) when `A` contains a prime `p ≥ |A|`. If some
`b ∈ A` is not a multiple of `p`, the pair `(p, b)` has gcd 1 and `1 ≤ p / |A|`. Otherwise every
element is a multiple of `p` at most `max A`, so `|A| ≤ max A / p`, and the pair `(max A, p)` has
gcd `p ≤ max A / |A|`. -/

theorem Opn.erdos_402_large_prime :
    ∀ (A : Finset ℕ), 0 ∉ A → ∀ p ∈ A, p.Prime → A.card ≤ p →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
