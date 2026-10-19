import Mathlib
import Nodes.«spec-a70fcca4».Context

/-- The natural counterexample candidate for Erdős 257, stated so that it can be proved or
refuted: `1/2` is the Mersenne reciprocal sum of some infinite set. A finite set cannot give
`1/2` (finite sums have odd denominators), so any representation of `1/2` is infinite, and a
proof of this statement refutes the root. The greedy walk for `1/2` (the only possible
representation) begins 2, 3, 6, 7, 14, 20, 21, 26, 27, 32, ... and has been run without stalling
to depth 2500 here and to depth 10^8 by Hong (Zenodo 23287959, 2026, unrefereed); Kovač
(erdosproblems.com/257, Aug 2025) expects the subset-sum set, a fat Cantor set, to contain
such rationals. No proof in either direction is known. -/
theorem Opn.erdos_257_half_is_a_subsum :
    ∃ A : Set ℕ, A.Infinite ∧ ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = 1 / 2 := by
  sorry
