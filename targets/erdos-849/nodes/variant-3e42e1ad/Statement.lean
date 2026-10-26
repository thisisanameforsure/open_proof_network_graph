import Mathlib
import Nodes.«variant-3e42e1ad».Context

open Nat

/-- The cases $t = 1$ and $t = 2$ of Erdős 849 each hold for infinitely many $a$: for every $N$
there are $a, b \ge N$ with $a$ in exactly one row and $b$ in exactly two rows (rows $n$ with
$\binom{n}{k} = a$, $1 \le k \le n/2$). The proof takes a prime $a = p$ (only $\binom{p}{1}$) and
$b = \binom{p}{2}$ for a prime $p \ge 7$ (only $\binom{p}{2}$ and $\binom{b}{1}$), since a prime
dividing $\binom{n}{k}$ is at most $n$. -/
theorem Opn.erdos_849_one_and_two_rows_infinitely_often :
    ∀ N : ℕ, (∃ a ≥ N, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 1) ∧
      (∃ a ≥ N, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 2) := by
  sorry
