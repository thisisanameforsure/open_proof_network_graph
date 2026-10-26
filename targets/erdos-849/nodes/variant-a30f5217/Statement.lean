import Mathlib
import Nodes.«variant-a30f5217».Context

open Nat

/-- Erdős 849, the elementary upper bound on multiplicity (the half-triangle form of
Singmaster's 1971 bound `N(a) = O(log a)`): the number of rows `n` in which `a` appears as
`C(n, k)` with `1 ≤ k ≤ n/2` is at most `⌊log₂ a⌋`. Each `k` gives at most one row, since
`C(·, k)` is strictly increasing, and a row with `C(n, k) = a` has `2^k ≤ C(2k, k) ≤ a`. -/
theorem Opn.erdos_849_rows_ncard_le_log : ∀ a : ℕ,
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard ≤ Nat.log 2 a := by
  sorry
