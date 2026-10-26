import Mathlib
import Nodes.«variant-72919549».Context

open Nat

/-- Infinitely many integers $a$ are $\binom{n}{k}$ with $1 \le k \le n/2$ in at least three rows
$n$: for every $N$ there is such an $a \ge N$. A consequence of the affirmative answer to
Erdős 849 (it gives one $a$ for each $t \ge 3$, all distinct). The proof uses Singmaster's
Fibonacci family: for $i \ge 1$, $n = F_{2i+2}F_{2i+3}$ and $k = F_{2i}F_{2i+3}$ give
$\binom{n}{k} = \binom{n-1}{k+1}$, and with $\binom{a}{1}$ that is three rows. -/
theorem Opn.erdos_849_three_rows_infinitely_often :
    ∀ N : ℕ, ∃ a ≥ N, 3 ≤ {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard := by
  sorry
