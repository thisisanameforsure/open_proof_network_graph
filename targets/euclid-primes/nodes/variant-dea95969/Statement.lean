import Defs.IsPrime
import Mathlib.Tactic

/-! Infinitely many primes congruent to 3 modulo 4, over the graph's own `IsPrime`: for every
`n` there is a prime `p > n` with `p % 4 = 3`. A strengthening of Euclid's theorem (the root). -/

theorem Opn.infinitude_of_primes_three_mod_four : ∀ n : Nat, ∃ p : Nat, n < p ∧ Opn.IsPrime p ∧ p % 4 = 3 := by
  sorry
