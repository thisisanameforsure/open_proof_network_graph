import Mathlib
import Nodes.«variant-0691f5bb».Context

open Nat

/-- Erdős 849 for $t = 2$: some integer $a$ is $\binom{n}{k}$ with $1 \le k \le n/2$ in exactly
2 rows $n$. The proof takes $a = 6$: rows 4 and 6 ($\binom{4}{2}=\binom{6}{1}$). -/
theorem Opn.erdos_849_t2 :
    ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 2 := by
  sorry
