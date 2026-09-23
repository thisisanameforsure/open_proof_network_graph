import Mathlib
import Nodes.«variant-3377fd96».Context

/-! Graham's gcd conjecture (Erdős problem 402) when some element `x` of `A` has no prime factor
below `|A|`: either `x` divides every element, and then the largest element is at least `|A| * x`,
or `gcd(x, b) < x` for some `b`, and then `x / gcd(x, b)` is a divisor of `x` above 1, so at
least `x.minFac ≥ |A|`. Contains the case of a prime `p ≥ |A|` in `A`. -/

theorem Opn.erdos_402_minFac :
    ∀ (A : Finset ℕ), 0 ∉ A → ∀ x ∈ A, A.card ≤ x.minFac →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
