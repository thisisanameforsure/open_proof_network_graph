import Mathlib
import Nodes.«variant-d08712d9».Context

/-- Erdős 257 for `A` the sums of two squares `{a² + b²}`. Known: D. Duverney and Y. Tachiya,
*Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*,
Forum Math. 31 (2019), 1557–1566, Example 1.2 (a case of Corollary 1.2 with `s = ∞` and `E`
the prime `2`, the primes `≡ 1 (mod 4)` and the squares of the primes `≡ 3 (mod 4)`): `1` and
`∑_{n ≥ 1} 1/(q^(j s_n^i) - 1)` are linearly independent over `ℚ` for every integer `|q| > 1`,
where `s_n` runs over the positive sums of two squares; take `q = 2`, `i = j = 1`. The element
`0 = 0² + 0²` contributes `1/0 = 0` in Lean. -/
theorem Opn.erdos_257_sums_of_two_squares :
    Irrational (∑' m : {m : ℕ | ∃ a b, m = a ^ 2 + b ^ 2}, (1 : ℝ) / (2 ^ m.1 - 1)) := by
  sorry
