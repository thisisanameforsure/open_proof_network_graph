import Defs.IsPrime
import Mathlib.Tactic
import Nodes.«variant-aceabdc4».Context

/-! Infinitely many primes that are at least 100, over the graph's own `Opn.IsPrime`: for every
`n` there is a prime `p` with `n < p` and `100 ≤ p`. A consequence of the root
`Opn.infinitude_of_primes` (apply it at `max n 100`), which this node declares as a dependency (D-30 label: related). -/

theorem Opn.infinitude_of_primes_at_least_hundred : ∀ n : Nat, ∃ p : Nat, n < p ∧ 100 ≤ p ∧ Opn.IsPrime p := by
  sorry
