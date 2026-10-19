import Mathlib
import Nodes.«spec-ddd99827».Context

/-- Each term of the Mersenne reciprocal series exceeds the sum of all later terms:
`∑_{m > n} 1/(2^m - 1) < 1/(2^n - 1)` for `n ≥ 1`. This is the gap condition that makes the
subset sums `∑_{a ∈ A} 1/(2^a - 1)` a Cantor set in which every point has exactly one
representation (Kovač–Tao, arXiv:2406.17593, Remark 4.1); every greedy or counting attack on
Erdős 257 rests on it. -/
theorem Opn.erdos_257_tail_lt_term (n : ℕ) (hn : 1 ≤ n) :
    ∑' k : ℕ, (1 : ℝ) / (2 ^ (n + 1 + k) - 1) < 1 / (2 ^ n - 1) := by
  sorry
