theorem witness : ∃ (A : Set ℕ), A.Infinite ∧ (0 : ℕ) ∉ A ∧
    ∀ m ∈ A, ∀ n ∈ A, n < m → n ∣ m := by
  refine ⟨Set.range (fun k : ℕ => 2 ^ k),
    Set.infinite_range_of_injective (Nat.pow_right_injective (le_refl 2)), ?_, ?_⟩
  · rintro ⟨k, hk⟩
    exact absurd hk (by positivity)
  · rintro m ⟨i, rfl⟩ n ⟨j, rfl⟩ h
    simp only at h ⊢
    have hji : j < i := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h
    exact Nat.pow_dvd_pow 2 hji.le
