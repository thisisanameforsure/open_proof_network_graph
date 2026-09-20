import Defs.IsPrime
import Mathlib.Tactic
import Nodes.«variant-6e71b160».Context

/-! Infinitely many primes that are at least 100, over the graph's own `Opn.IsPrime`: for every
`n` there is a prime `p` with `n < p` and `100 ≤ p`. The bound is inclusive and is written in the
style of `Opn.Divides`, as `∃ k, p = 100 + k`. A consequence of the root
`Opn.infinitude_of_primes` (apply it at `max n 100`), which this node declares as a dependency. -/

theorem Opn.infinitude_of_primes_ge_hundred : ∀ n : Nat, ∃ p : Nat, n < p ∧ (∃ k : Nat, p = 100 + k) ∧ Opn.IsPrime p := by
  sorry
