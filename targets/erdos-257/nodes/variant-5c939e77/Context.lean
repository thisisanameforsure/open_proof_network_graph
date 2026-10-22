import Mathlib

/-! Declared dependencies (D-4 step 8): `spec-5e2e0890`. -/

/-- Uniqueness of representation: two sets of positive integers with the same Mersenne
reciprocal sum are equal. It follows from the gap `∑_{m > n} 1/(2^m - 1) < 1/(2^n - 1)` by
looking at the least element of the symmetric difference. Consequence for Erdős 257: a rational
`x` is a subset sum for at most one `A`, found by the greedy walk (take `n` whenever the
remainder is at least `1/(2^n - 1)`), so the affirmative statement is false iff some rational
with an even denominator (such as `1/2`, whose representation cannot be finite) is reached by
a greedy walk that never stalls. -/
theorem Opn.erdos_257_subsum_injective (A B : Set ℕ) (hA : 0 ∉ A) (hB : 0 ∉ B)
    (h : ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = ∑' n : B, (1 : ℝ) / (2 ^ n.1 - 1)) :
    A = B := by
  sorry
