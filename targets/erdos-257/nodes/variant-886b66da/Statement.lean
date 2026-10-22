import Mathlib
import Nodes.«variant-886b66da».Context

/-- Erdős 257 for every infinite arithmetic progression `A = {a + d n : n ≥ 0}` (`d ≥ 1`).
Known: for `a = 0` this is Erdős 1948 at base `t = 2^d` (J. Indian Math. Soc. 12, 63–66,
Theorem); for `a ≥ 1`, `1/(2^(a+dn) - 1) = 2^(-a)/(t^n + q)` with `t = 2^d` and `q = -2^(-a)`, so
it follows from P. B. Borwein, *On the irrationality of ∑ 1/(q^n + r)*, J. Number Theory 37
(1991), 253–259: `∑_{n ≥ 1} 1/(t^n + q)` is irrational for every integer `t ≥ 2` and rational
`q ∉ {0, -t^n}` (as stated by Kovač–Tao, arXiv:2406.17593, §2.1.2). The even and the odd
integers are the cases `d = 2`. A `0` in `A` contributes `1/0 = 0` in Lean. -/
theorem Opn.erdos_257_arithmetic_progressions :
    ∀ a d : ℕ, 0 < d →
      Irrational (∑' m : {m : ℕ | ∃ n, m = a + d * n}, (1 : ℝ) / (2 ^ m.1 - 1)) := by
  sorry
