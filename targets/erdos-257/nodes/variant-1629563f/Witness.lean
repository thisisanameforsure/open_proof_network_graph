import Mathlib

theorem witness : ∃ (A : Set ℕ), A.Infinite ∧ (0 : ℕ) ∉ A ∧
    ∀ C : ℕ, ∃ m ∈ A, ∃ L : ℕ, 0 < L ∧ (∀ a ∈ A, a < m → 2 ^ a - 1 ∣ L) ∧ 2 ^ C * L ≤ 2 ^ m := by
  refine ⟨Set.range (fun k : ℕ => 2 ^ k),
    Set.infinite_range_of_injective (Nat.pow_right_injective (le_refl 2)), ?_, ?_⟩
  · rintro ⟨k, hk⟩
    exact absurd hk (by positivity)
  · intro C
    refine ⟨2 ^ (C + 1), ⟨C + 1, rfl⟩, 2 ^ (2 ^ C) - 1, ?_, ?_, ?_⟩
    · have : 2 ≤ 2 ^ (2 ^ C) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 ^ C) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
      omega
    · rintro a ⟨j, rfl⟩ hj
      simp only at hj ⊢
      have hjC : j ≤ C := by
        have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hj
        omega
      exact Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.pow_dvd_pow 2 hjC)
    · have h1 : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
      calc 2 ^ C * (2 ^ (2 ^ C) - 1) ≤ 2 ^ C * 2 ^ (2 ^ C) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = 2 ^ (C + 2 ^ C) := by rw [pow_add]
        _ ≤ 2 ^ (2 ^ (C + 1)) := Nat.pow_le_pow_right (by norm_num) (by rw [pow_succ]; omega)
