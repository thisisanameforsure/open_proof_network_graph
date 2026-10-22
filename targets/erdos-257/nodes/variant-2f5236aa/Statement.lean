import Mathlib
import Nodes.«variant-2f5236aa».Context

/-- Erdős 257 for `A = ℕ`: the Erdős–Borwein constant `∑_{n ≥ 1} 1/(2^n - 1) = ∑_{n ≥ 1} d(n)/2^n`
is irrational. Known: P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math.
Soc. (N.S.) 12 (1948), 63–66, Theorem (`f(1/t)` irrational for every integer `|t| > 1`; here
`t = 2`). The `n = 0` term is `1/0 = 0` in Lean, so the sum is the sum over `n ≥ 1`. -/
theorem Opn.erdos_257_all_naturals :
    Irrational (∑' n : ℕ, (1 : ℝ) / (2 ^ n - 1)) := by
  sorry
