import Defs.IsPrime
import Mathlib.Tactic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Nat.Prime.Infinite

/-! The set of primes is infinite, over the graph's own `Opn.IsPrime` (D-30 variant of Euclid's
theorem, whose root says: for every `n` there is a prime greater than `n`). -/

theorem Opn.setOf_isPrime_infinite : {p : Nat | Opn.IsPrime p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
  refine ⟨p, ⟨hp.two_le, ?_⟩, by omega⟩
  rintro d ⟨c, hc⟩
  exact (Nat.dvd_prime hp).mp ⟨c, hc⟩
