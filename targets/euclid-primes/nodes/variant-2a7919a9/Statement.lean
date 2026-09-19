import Defs.IsPrime
import Mathlib.Tactic

/-! Euclid's original formulation (Elements IX.20): no finite list contains all the primes.
Over the graph's own `Opn.IsPrime`: for every list of natural numbers there is a prime that is
not a member of it. -/

theorem Opn.no_finite_list_of_primes : ∀ l : List Nat, ∃ p : Nat, Opn.IsPrime p ∧ p ∉ l := by
  sorry
