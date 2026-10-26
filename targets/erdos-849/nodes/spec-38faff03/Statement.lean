import Mathlib
import Nodes.«spec-38faff03».Context

open Nat

/-- Erdős 849, structure: every row that holds the value `a` at some `1 ≤ k ≤ n/2` satisfies
`2 ≤ n ≤ a`, because `C(n, k) ≥ C(n, 1) = n` there. So each solution set is finite, and a
search for the rows holding `a` need only look at `n ≤ a`. -/
theorem Opn.erdos_849_rows_le : ∀ a : ℕ,
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a} ⊆ Set.Icc 2 a := by
  sorry
