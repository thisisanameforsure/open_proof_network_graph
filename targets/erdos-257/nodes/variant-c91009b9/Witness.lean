import Mathlib

theorem witness : ∃ (A : Set ℕ), A.Infinite ∧ A.Pairwise Nat.Coprime ∧
    Summable fun (n : A) => (1 : ℝ) / (n.1 : ℝ) := by
  refine ⟨(fun p => p ^ 2) '' {p : ℕ | p.Prime}, ?_, ?_, ?_⟩
  · exact Set.Infinite.image (fun x _ y _ h => Nat.pow_left_injective (by norm_num) h)
      Nat.infinite_setOf_prime
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := fun h => hne (by rw [h])
    exact Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp hq).2 hpq)
  · have hs : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.2 (by norm_num)
    have hinj : Function.Injective
        (fun n : ((fun p => p ^ 2) '' {p : ℕ | p.Prime}) => Nat.sqrt n.1) := by
      rintro ⟨_, p, hp, rfl⟩ ⟨_, q, hq, rfl⟩ h
      simp only [Nat.sqrt_eq'] at h
      subst h
      rfl
    refine (hs.comp_injective hinj).congr ?_
    rintro ⟨_, p, hp, rfl⟩
    simp [Nat.sqrt_eq']
