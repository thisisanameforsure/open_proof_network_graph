import Mathlib
import Nodes.«variant-d144ccc1».Context

/-- Erdős 257 for sets that are eventually lacunary of ratio two: if `A` is an infinite set of
positive integers and, from some point `N` on, any two elements `n < m` of `A` satisfy `m ≥ 2n`,
then `∑_{n ∈ A} 1/(2^n - 1)` is irrational. Examples: `{2^k}`, `{2^k - 1}`, `{3^k}`, `{k!}`, any
infinite divisibility chain, and any finite set joined to one of these.

Proof by Liouville's criterion (`Opn.erdos_257_liouville_criterion`): finitely many terms change
the sum by a rational, so assume the ratio condition for all pairs. Call `a ∈ A` non-doubling
when `2a ∉ A`. If infinitely many elements are non-doubling, then for `m ∈ A` the elements below
`m` sum to at most `m` minus the number of non-doubling ones among them (induction on the
largest), so the product of their `2^a - 1` is at most `2^(m - C)` once `C` non-doubling elements
lie below `m`. If finitely many are, all below `b`, then above `b` the set is a doubling chain,
every element of `A` from `b` to `n` divides `n`, and with `m = 2n` the common denominator
`(∏_{a ∈ A, a ≤ b} (2^a - 1)) · (2^n - 1)` is at most `2^(m - C)` for `n` large. Either way the
positive tail from `m` on, below `4 · 2^(-m)`, cannot be a positive multiple of `1/(qL)`.

Covered in principle by Erdős (Math. Student 36, 1968), who proves irrationality for pairwise
coprime `A` with summable reciprocals and remarks that coprimality can be dropped; ratio
below two is beyond this elementary argument. -/
theorem Opn.erdos_257_eventually_ratio_two :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∃ N : ℕ, ∀ m ∈ A, ∀ n ∈ A, N ≤ n → n < m → 2 * n ≤ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
