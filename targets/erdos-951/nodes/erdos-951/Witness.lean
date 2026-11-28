open scoped Finsupp Nat.Prime Topology
open Filter
open Erdos951

/-! Non-vacuity witness (D-4 step 7): the primes in increasing order, `a i = nth Prime i`, start above 1, increase strictly, and by unique factorisation two distinct exponent vectors give distinct natural numbers, so their Beurling integers differ by at least 1. -/

theorem witness : ∃ (a : ℕ → ℝ), (1 : ℝ) < a (0 : ℕ) ∧ StrictMono a ∧ Erdos951.Erdos951Prop a := by
  have hinf := Nat.infinite_setOfPred_prime
  have pinj : Function.Injective (Nat.nth Nat.Prime) := Nat.nth_injective hinf
  refine ⟨fun i => ((Nat.nth Nat.Prime i : ℕ) : ℝ), ?_, ?_, ?_⟩
  · show (1 : ℝ) < ((Nat.nth Nat.Prime 0 : ℕ) : ℝ)
    rw [Nat.nth_prime_zero_eq_two]
    norm_num
  · intro i j h
    show ((Nat.nth Nat.Prime i : ℕ) : ℝ) < ((Nat.nth Nat.Prime j : ℕ) : ℝ)
    exact Nat.cast_lt.mpr (Nat.nth_strictMono hinf h)
  · intro k l hkl
    have key : ∀ f : ℕ →₀ ℕ, (f.mapDomain (Nat.nth Nat.Prime)).prod (fun x y => x ^ y)
        = f.prod (fun x y => Nat.nth Nat.Prime x ^ y) :=
      fun f => Finsupp.prod_mapDomain_index_inj pinj
    have hcast : ∀ f : ℕ →₀ ℕ,
        beurlingInteger (fun i => ((Nat.nth Nat.Prime i : ℕ) : ℝ)) f
          = ((f.prod fun x y => Nat.nth Nat.Prime x ^ y : ℕ) : ℝ) := by
      intro f
      simp [beurlingInteger, Finsupp.prod, Nat.cast_prod, Nat.cast_pow]
    have hfac : ∀ f : ℕ →₀ ℕ, (f.prod fun x y => Nat.nth Nat.Prime x ^ y).factorization
        = f.mapDomain (Nat.nth Nat.Prime) := by
      intro f
      rw [← key]
      apply Nat.prod_pow_factorization_eq_self
      intro q hq
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hq)
      exact Nat.prime_nth_prime i
    have hne : (k.prod fun x y => Nat.nth Nat.Prime x ^ y)
        ≠ (l.prod fun x y => Nat.nth Nat.Prime x ^ y) := by
      intro h
      apply hkl
      apply Finsupp.mapDomain_injective pinj
      rw [← hfac, ← hfac, h]
    rw [hcast, hcast, ge_iff_le]
    have hz : ((k.prod fun x y => Nat.nth Nat.Prime x ^ y : ℕ) : ℤ)
        - ((l.prod fun x y => Nat.nth Nat.Prime x ^ y : ℕ) : ℤ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hne)
    have h1 := Int.one_le_abs hz
    exact_mod_cast h1
