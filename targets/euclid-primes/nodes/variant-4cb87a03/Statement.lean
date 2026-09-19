import Defs.IsPrime
import Mathlib.Tactic

/-! Euclid's explicit bound, over the graph's own `IsPrime`: for every `n` there is a prime `p`
with `n < p ≤ n! + 1`. A strengthening of the root `Opn.infinitude_of_primes` (drop the middle
conjunct to recover it). `n !` is Mathlib's `Nat.factorial`, as in the root's merged holes. -/

theorem Opn.euclid_explicit_bound : ∀ n : Nat, ∃ p : Nat, n < p ∧ p ≤ Nat.factorial n + 1 ∧ Opn.IsPrime p := by
  sorry
