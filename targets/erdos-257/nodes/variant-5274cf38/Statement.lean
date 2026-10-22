import Mathlib
import Nodes.«variant-5274cf38».Context

/-- Erdős 257 for every infinite `A` whose indicator is eventually periodic (for example any
arithmetic progression, the odd numbers, any union of residue classes, changed in finitely many
places). Known: F. Luca and Y. Tachiya, *Irrationality of Lambert series associated with a
periodic sequence*, Int. J. Number Theory 10 (2014), 623–636, Theorem 1.1 (restated as Theorem A,
RIMS Kôkyûroku 2014 (2017), p. 139): `∑ a(n)/(q^n - 1)` is irrational for every purely periodic
integer sequence `a`, not identically zero, and every integer `|q| > 1`. An eventually periodic
infinite `A` differs from a nonempty purely periodic set in finitely many places, which changes
the sum by a rational number. -/
theorem Opn.erdos_257_eventually_periodic :
    ∀ A : Set ℕ, A.Infinite →
      (∃ p N : ℕ, 0 < p ∧ ∀ n, N ≤ n → (n ∈ A ↔ n + p ∈ A)) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
