import Mathlib
import Nodes.«variant-970a2ffa».Context

/-- Erdős 257 for `A` the squarefree numbers. Known: D. Duverney and Y. Tachiya, *Refinement of
the Chowla–Erdős method and linear independence of certain Lambert series*, Forum Math. 31
(2019), 1557–1566, Example 1.1 (a case of Corollary 1.2 with `s = 2`, `q = 2`): `1` and
`∑ |μ(n)|/(2^n - 1)` are linearly independent over `ℚ`. -/
theorem Opn.erdos_257_squarefree :
    Irrational (∑' n : {n : ℕ | Squarefree n}, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
