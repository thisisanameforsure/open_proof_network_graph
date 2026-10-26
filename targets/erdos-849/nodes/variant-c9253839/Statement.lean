import Mathlib
import Nodes.«variant-c9253839».Context

open Nat

/-- Erdős 849 for $t = 4$: some integer $a$ is $\binom{n}{k}$ with $1 \le k \le n/2$ in exactly
4 rows $n$. The proof takes $a = 3003$: rows 14, 15, 78 and 3003 ($\binom{14}{6}=\binom{15}{5}=\binom{78}{2}=\binom{3003}{1}$). -/
theorem Opn.erdos_849_t4 :
    ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 4 := by
  sorry
