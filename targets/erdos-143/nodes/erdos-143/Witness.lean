open Filter Finset
open scoped Topology
open Erdos143

/-! Non-vacuity witness (D-4 step 7): the primes, as reals, form an infinite countable set above 1, and for distinct primes p, q and k ≥ 1 the integer k p - q is never zero, so |k p - q| ≥ 1. -/

theorem witness : ∃ (A : Set ℝ), WellSeparatedSet A := by
  refine ⟨(fun p : ℕ => (p : ℝ)) '' {p | p.Prime}, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simp only [Set.mem_Ioi]
    exact_mod_cast (show (1 : ℕ) < p from hp.one_lt)
  · exact Set.Infinite.image (fun _ _ _ _ h => Nat.cast_injective h) Nat.infinite_setOf_prime
  · exact (Set.to_countable _).image _
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne k hk
    have hpq : p ≠ q := fun h => hne (by rw [h])
    have hz : ((k : ℤ) * p - q) ≠ 0 := by
      intro h
      have h' : k * p = q := by exact_mod_cast sub_eq_zero.mp h
      have hdvd : p ∣ q := ⟨k, by rw [← h', mul_comm]⟩
      rcases (Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd with h''
      exact hpq h''
    have h1 := Int.one_le_abs hz
    have : |(k : ℝ) * (p : ℝ) - (q : ℝ)| = (( |(k : ℤ) * p - q| : ℤ) : ℝ) := by
      push_cast; rfl
    rw [this]
    exact_mod_cast h1
