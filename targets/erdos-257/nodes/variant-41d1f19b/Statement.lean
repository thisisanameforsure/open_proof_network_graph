import Mathlib
import Nodes.«variant-41d1f19b».Context

/-- Erdős 257 for sets with arbitrarily long gaps: let `A` be an infinite set of positive
integers such that, for every `C`, some `m ∈ A` exceeds the sum of all elements of `A` below it
by at least `C`. Then `∑_{n ∈ A} 1/(2^n - 1)` is irrational.

The hypothesis allows long dense blocks between the gaps, so the reciprocal sum `∑_{n ∈ A} 1/n`
may diverge: for `A = ⋃_j [X_j, 2X_j]` with `X_{j+1} = 4X_j^2` each block contributes more than
`1/2` to it, while the elements below `X_{j+1}` sum to less than `3X_j^2`. Such sets are covered
neither by Erdős (Math. Student 36, 1968), whose sets have summable reciprocals, nor by the
periodic and multiplicative cases listed in the literature record.

Proof (Liouville's criterion, `Opn.erdos_257_liouville_criterion`, with the product of the
`2^a - 1` over the elements below `m` as the common denominator, which is at most
`2^(m - C)`). -/
theorem Opn.erdos_257_long_gaps :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∀ C : ℕ, ∃ m ∈ A, ∃ F : Finset ℕ, (∀ a, a ∈ F ↔ a ∈ A ∧ a < m) ∧ C + ∑ a ∈ F, a ≤ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
