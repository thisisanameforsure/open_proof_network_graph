import Mathlib

/-! Declared dependencies (D-4 step 8): `spec-440db0f9`. -/

/-- erdos-1050, hole hden (erdos-1050--h1-v2--h3), ingredient 1 of annex 4670684d2f0d on that node:
the Gaussian binomial coefficient at q = 2, written as the same product of quotients that `Qc` in
h3 and h4 uses, is an integer. For k > n a factor 2^(n - i) - 1 with truncated n - i = 0 is 0, so
the product is 0 there, which is also the Gaussian binomial's value. -/
theorem erdos_1050_gauss_binom_two_int (n k : ℕ) :
    ∃ z : ℤ, (z : ℚ) = ∏ i ∈ Finset.range k, ((2 : ℚ) ^ (n - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1) := by
  sorry
