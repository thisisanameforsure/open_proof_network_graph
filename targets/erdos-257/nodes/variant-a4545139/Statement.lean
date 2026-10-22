import Mathlib
import Nodes.«variant-a4545139».Context

/-- Divisibility-chain case of Erdős 257: if `A` is an infinite set of positive integers in
which the smaller of any two elements divides the larger (for example `{2^k}`, `{d · 2^k}` or
`{k!}`), then `∑_{n ∈ A} 1/(2^n - 1)` is irrational. Proof (Liouville's argument with a common
denominator): take `n ∈ A` large and `m` the next element of `A`; every element of `A` up to `n`
divides `n`, so `2^a - 1` divides `2^n - 1` and the partial sum up to `n` has denominator
`2^n - 1`, while `n ∣ m`, `n < m` give `m ≥ 2n`, so the positive tail from `m` on is below
`4 · 2^(-2n)`; a rational `p/q` would force `1 ≤ 4q · 2^(-n)` for every such `n`. A special case
of Erdős's remark (Math. Student 36, 1968) that his theorem for pairwise coprime `A` with summable
reciprocals holds without coprimality; here the elements are as far from coprime as possible. -/
theorem Opn.erdos_257_divisibility_chain :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∀ m ∈ A, ∀ n ∈ A, n < m → n ∣ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
