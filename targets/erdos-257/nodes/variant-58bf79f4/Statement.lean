import Mathlib
import Nodes.«variant-58bf79f4».Context

/-- Liouville's criterion for Erdős 257: let `A` be an infinite set of positive integers such
that, for every `C`, some `m ∈ A` has a common multiple `L` of the numbers `2^a - 1` over the
elements `a < m` of `A` with `2^C · L ≤ 2^m` (the elements below `m` have a small common
denominator compared with the gap the tail leaves). Then `∑_{n ∈ A} 1/(2^n - 1)` is irrational.
Proof: if the sum were `p/q`, take `C` with `2^C > 4q`; with `L` as above, `q · L` times the tail
from `m` on is a positive integer, but the tail is below `4 · 2^(-m)`, so it is below
`4q · 2^(-C) < 1`. The criterion covers the lacunary sets (any two elements `n < m` with
`m ≥ 2n + 1`, taking `L` the product of the `2^a - 1`; node `variant-48473144`) and the
divisibility chains (`{2^k}`, `{k!}`, taking `L = 2^n - 1` for the largest `n < m`; node
`variant-a4545139`). It does not reach sets of positive density, nor lacunary sets of ratio 2
in general; those need Erdős's arguments (1948, 1968). -/
theorem Opn.erdos_257_liouville_criterion :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∀ C : ℕ, ∃ m ∈ A, ∃ L : ℕ, 0 < L ∧ (∀ a ∈ A, a < m → 2 ^ a - 1 ∣ L) ∧ 2 ^ C * L ≤ 2 ^ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
