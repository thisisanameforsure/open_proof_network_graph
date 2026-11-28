open CongruentNumber

/-! Non-vacuity witness (D-4 step 7): n = 5 is squarefree and odd, and both `A 5` and `B 5` are empty (2x² + y² is never 5 mod 8), so 2·|A 5| = |B 5| = 0. -/

theorem witness : ∃ (n : ℕ), Squarefree n ∧ Odd n ∧ 2 * (A n).ncard = (B n).ncard := by
  have mod8 : ∀ x y : ℤ, (2 * x ^ 2 + y ^ 2) % 8 ≠ 5 := by
    intro x y
    have hx := Int.emod_emod_of_dvd x (by norm_num : (8 : ℤ) ∣ 8)
    have : (2 * x ^ 2 + y ^ 2) % 8 = (2 * (x % 8) ^ 2 + (y % 8) ^ 2) % 8 := by
      simp [pow_two, Int.add_emod, Int.mul_emod]
    rw [this]
    have h1 : 0 ≤ x % 8 := Int.emod_nonneg x (by norm_num)
    have h2 : x % 8 < 8 := Int.emod_lt_of_pos x (by norm_num)
    have h3 : 0 ≤ y % 8 := Int.emod_nonneg y (by norm_num)
    have h4 : y % 8 < 8 := Int.emod_lt_of_pos y (by norm_num)
    interval_cases (x % 8) <;> interval_cases (y % 8) <;> decide
  have hA : A 5 = ∅ := by
    ext ⟨x, y, z⟩
    simp only [A, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    apply mod8 x y
    have : (2 * x ^ 2 + y ^ 2) = 5 - 32 * z ^ 2 := by push_cast at h; linarith
    rw [this]; omega
  have hB : B 5 = ∅ := by
    ext ⟨x, y, z⟩
    simp only [B, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    apply mod8 x y
    have : (2 * x ^ 2 + y ^ 2) = 5 - 8 * z ^ 2 := by push_cast at h; linarith
    rw [this]; omega
  refine ⟨5, (by norm_num : Nat.Prime 5).squarefree, ⟨2, rfl⟩, ?_⟩
  rw [hA, hB]; simp
