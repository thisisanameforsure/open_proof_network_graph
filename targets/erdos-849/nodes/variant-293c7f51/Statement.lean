import Mathlib
import Nodes.«variant-293c7f51».Context

open Nat

/-- Erdős 849 for $t = 3$: some integer $a$ is $\binom{n}{k}$ with $1 \le k \le n/2$ in exactly
3 rows $n$. The proof takes $a = 120$: rows 10, 16 and 120 ($\binom{10}{3}=\binom{16}{2}=\binom{120}{1}$). -/
theorem Opn.erdos_849_t3 :
    ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 3 := by
  sorry
