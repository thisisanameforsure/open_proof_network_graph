import Mathlib
import Nodes.«variant-7a0f5735».Context

/-- Erdős 257 for `A` the perfect `k`-th powers `{n^k}`, for every `k ≥ 1`. Known: D. Duverney
and Y. Tachiya, *Refinement of the Chowla–Erdős method and linear independence of certain
Lambert series*, Forum Math. 31 (2019), 1557–1566, Corollary 1.2 with `s = ∞` and `E` the
primes (so `F_∞` is all positive integers): `1` and the numbers `∑_{n ≥ 1} 1/(q^(j n^i) - 1)`
are linearly independent over `ℚ` for every integer `|q| > 1`; take `q = 2`, `j = 1`, `i = k`.
The element `0 = 0^k` contributes `1/0 = 0` in Lean. -/
theorem Opn.erdos_257_perfect_powers :
    ∀ k : ℕ, 0 < k →
      Irrational (∑' m : {m : ℕ | ∃ n, m = n ^ k}, (1 : ℝ) / (2 ^ m.1 - 1)) := by
  sorry
