import Mathlib
import Nodes.«variant-1629563f».Context

/-- Liouville's criterion for Erdős 257: let `A` be an infinite set of positive integers such
that, for every `C`, some `m ∈ A` has a common multiple `L` of the numbers `2^a - 1` over the
elements `a < m` of `A` with `2^C · L ≤ 2^m` (the elements below `m` have a small common
denominator compared with the gap the tail leaves). Then `∑_{n ∈ A} 1/(2^n - 1)` is irrational.
Proof: if the sum were `p/q`, take `C` with `2^C > 4q`; with `L` as above, `q · L` times the tail
from `m` on is a positive integer, but the tail is below `4 · 2^(-m)`, so it is below
`4q · 2^(-C) < 1`. The criterion covers every set that is eventually lacunary of ratio two
(`Opn.erdos_257_eventually_ratio_two`: `{2^k}`, `{2^k - 1}`, `{3^k}`, `{k!}`, divisibility
chains). It does not reach sets of positive density, nor lacunary sets of ratio below two in
general; those need Erdős's arguments (1948, 1968). -/
theorem Opn.erdos_257_liouville_criterion :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∀ C : ℕ, ∃ m ∈ A, ∃ L : ℕ, 0 < L ∧ (∀ a ∈ A, a < m → 2 ^ a - 1 ∣ L) ∧ 2 ^ C * L ≤ 2 ^ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
