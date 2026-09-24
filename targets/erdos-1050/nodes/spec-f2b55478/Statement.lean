import Mathlib
import Nodes.«spec-f2b55478».Context

/-- erdos-1050, Borwein's route (annexes f593a93a8960 and 3ada4f0922d7 on erdos-1050--h1-v2):
the coefficient of x^m, for m > n, in Q_n(x) * f(x), where f(x) = sum_{k >= 1} x^k / (2^k - 1) and
Q_n(x) = sum_k (-1)^k 2^(k(k-1)/2) [n k]_2 [2n-k n]_2 x^k is the Pade denominator, equals
2^(n^2) (2;2)_n [m-n-1 n]_2 / prod_{j <= n} (2^(m-j) - 1). It vanishes for n < m <= 2n (the Pade
condition) and is positive for m > 2n, which makes the Pade remainder positive. Checked exactly for
n <= 15, m <= 3n + 29. -/
theorem erdos_1050_pade_remainder_coeff (n m : ℕ) (hnm : n < m) :
    ∑ j ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ j * (2 : ℚ) ^ (j * (j - 1) / 2) *
        (∏ i ∈ Finset.range j, ((2 : ℚ) ^ (n - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) *
        (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (2 * n - j - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) /
        ((2 : ℚ) ^ (m - j) - 1) =
      (2 : ℚ) ^ (n * n) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (i + 1) - 1)) *
        (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (m - n - 1 - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) /
        ∏ j ∈ Finset.range (n + 1), ((2 : ℚ) ^ (m - j) - 1) := by
  sorry
