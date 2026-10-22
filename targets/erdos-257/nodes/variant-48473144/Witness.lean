theorem witness : ∃ (A : Set ℕ), A.Infinite ∧ (0 : ℕ) ∉ A ∧
    ∀ m ∈ A, ∀ n ∈ A, n < m → (2 : ℕ) * n + (1 : ℕ) ≤ m := by
  refine ⟨Set.range (fun k : ℕ => 3 ^ k),
    Set.infinite_range_of_injective (Nat.pow_right_injective (by norm_num : 2 ≤ 3)), ?_, ?_⟩
  · rintro ⟨k, hk⟩
    exact absurd hk (by positivity)
  · rintro m ⟨i, rfl⟩ n ⟨j, rfl⟩ h
    simp only at h ⊢
    have hji : j < i := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h
    have h1 : 3 ^ (j + 1) ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hji
    have h2 : 3 ^ (j + 1) = 3 * 3 ^ j := by ring
    have h3 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega
