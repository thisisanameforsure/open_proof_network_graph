import Mathlib
import Nodes.«variant-3d9db4a5».Context

open Nat

/-- Erdős 849 for $t = 1$: some integer $a$ is $\binom{n}{k}$ with $1 \le k \le n/2$ in exactly
1 row $n$. The proof takes $a = 2$: the row 2 only ($\binom{2}{1}$). -/
theorem Opn.erdos_849_t1 :
    ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 1 := by
  sorry
