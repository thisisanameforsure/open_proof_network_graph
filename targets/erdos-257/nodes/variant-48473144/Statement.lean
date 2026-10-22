import Mathlib
import Nodes.«variant-48473144».Context

/-- Lacunary case of Erdős 257: if `A` is an infinite set of positive integers in which any two
elements `n < m` satisfy `m ≥ 2n + 1` (for example `{2^k - 1}`, `{3^k}` or `{k! : k ≥ 2}`), then
`∑_{n ∈ A} 1/(2^n - 1)` is irrational. Proof (Liouville's argument): for `m ∈ A` the partial sum
over the elements of `A` below `m` has denominator at most `2^(sum of those elements)`, which the
gap condition bounds by `2^(m - k)` with `k` the number of those elements, while the remaining
tail is positive and below `4 · 2^(-m)`; a rational `p/q` would force `1 ≤ 4q · 2^(-k)` for every
`k`. A special case of Erdős (Math. Student 36, 1968), whose theorem needs pairwise coprime
elements with summable reciprocals and who remarks that coprimality can be dropped; here no
coprimality is assumed (`{2^k - 1}` and `{3^k}` are not pairwise coprime in general). -/
theorem Opn.erdos_257_lacunary :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∀ m ∈ A, ∀ n ∈ A, n < m → 2 * n + 1 ≤ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
