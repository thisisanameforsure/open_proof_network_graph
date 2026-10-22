import Mathlib
import Nodes.«variant-418ce3d7».Context

/-- Ratio-two case of Erdős 257: if `A` is an infinite set of positive integers in which any two
elements `n < m` satisfy `m ≥ 2n` (a lacunary set of ratio at least 2, such as `{2^k}`,
`{2^k - 1}`, `{3^k}`, `{k!}` or any divisibility chain), then `∑_{n ∈ A} 1/(2^n - 1)` is
irrational. Proof, by Liouville's criterion (node `variant-58bf79f4`): call `a ∈ A` non-doubling
when `2a ∉ A`. If there are infinitely many, then for `m ∈ A` the elements below `m` sum to at
most `m` minus the number of non-doubling ones among them (induction on the largest), so the
product of their `2^a - 1` is at most `2^(m - C)` once `C` non-doubling elements lie below `m`.
If there are finitely many, all below `b`, then above `b` the set is a doubling chain
`n, 2n, 4n, ...` and every element of `A` between `b` and `n` divides `n`; with `m = 2n` the
common denominator `(∏_{a ∈ A, a ≤ b} (2^a - 1)) · (2^n - 1)` is at most `2^(m - C)` for `n`
large. In both cases the positive tail from `m` on is below `4 · 2^(-m)`, which a rational `p/q`
forbids once `2^C > 4q`. Covered in principle by Erdős's remark (Math. Student 36, 1968) that
his theorem for pairwise coprime `A` with summable reciprocals holds without coprimality. -/
theorem Opn.erdos_257_ratio_two :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∀ m ∈ A, ∀ n ∈ A, n < m → 2 * n ≤ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
