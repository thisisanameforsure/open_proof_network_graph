import Mathlib
import Nodes.«spec-12191c69».Context

open Nat

/-- Erdős 849, structure: the root counts rows `n`; the problem counts solutions `(n, k)`.
For every `a` the two counts agree, because `C(n, ·)` is strictly increasing on
`0 ≤ k ≤ n/2`, so a row holds the value `a` at most once in that range. -/
theorem Opn.erdos_849_rows_eq_pairs : ∀ a : ℕ,
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard =
      {p : ℕ × ℕ | 1 ≤ p.2 ∧ 2 * p.2 ≤ p.1 ∧ choose p.1 p.2 = a}.ncard := by
  sorry
