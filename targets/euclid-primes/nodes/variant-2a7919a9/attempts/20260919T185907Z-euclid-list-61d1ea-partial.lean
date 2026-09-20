import Defs.IsPrime
import Mathlib.Tactic

/-! Euclid's original formulation (Elements IX.20): no finite list contains all the primes.
Over the graph's own `Opn.IsPrime`: for every list of natural numbers there is a prime that is
not a member of it. -/

theorem Opn.no_finite_list_of_primes : ∀ l : List Nat, ∃ p : Nat, Opn.IsPrime p ∧ p ∉ l := by
  -- annex: 953980ae801a27640ee2c25f5aa7e507ef685e6fe040383ea0f025741be4e765
  intro l
  have bound : ∀ x : Nat, x ∈ l → x ≤ l.sum := sorry
  have euclid : ∃ p : Nat, l.sum < p ∧ Opn.IsPrime p := sorry
  obtain ⟨p, hlt, hp⟩ := euclid
  refine ⟨p, hp, fun hmem => ?_⟩
  have := bound p hmem
  omega
