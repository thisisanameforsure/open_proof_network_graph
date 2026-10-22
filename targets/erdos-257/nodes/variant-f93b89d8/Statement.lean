import Mathlib
import Nodes.«variant-f93b89d8».Context

/-- Erdős 257 for the union of the powers of two integer bases `2 ≤ a < b`:
`∑_{n ∈ {a^k} ∪ {b^k}} 1/(2^n - 1)` is irrational. This generalises
`Opn.erdos_257_powers_of_two_and_three` (the case `a = 2`, `b = 3`) to every pair of bases, with
no independence condition on `a` and `b`. Each part is a divisibility chain, so below `m` the
partial sum has the common denominator `(2^(a^J) - 1)(2^(b^K) - 1)`, where `a^J` and `b^K` are
the largest powers below `m`, and Liouville's criterion (`Opn.erdos_257_liouville_criterion`)
applies once `m - a^J - b^K` is unbounded along such `m`. Put `Z = b^(K+1)` and let `a^J` be the
largest power of `a` with `a^J ≤ Z`. Either `m = Z` has margin `Z - b^K - a^J ≥ C`, or `a^J` lies
within `b^K + C` of `Z`; in that case `m = a^(J+1)` (when `a ≥ 3`) or `m = 2^(J+2)` (when `a = 2`
and `b ≥ 4`) has margin at least `2 b^K - 2C`. Only the pair `(2, 3)` needs more: there the
Diophantine step `|2^y - 3·2^x| ≥ 2^x` from the proof of the two-and-three case is used. The
proof is elementary and complete. -/
theorem Opn.erdos_257_powers_of_two_bases :
    ∀ a b : ℕ, 2 ≤ a → a < b →
    Irrational (∑' n : ({n | ∃ k : ℕ, n = a ^ k} ∪ {n | ∃ k : ℕ, n = b ^ k} : Set ℕ),
      (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
