import Mathlib

theorem witness : ∃ (A : Set ℕ), A.Infinite ∧ (0 : ℕ) ∉ A ∧
    ∃ N : ℕ, ∀ m ∈ A, ∀ n ∈ A, N ≤ n → n < m → (2 : ℕ) * n ≤ m := by
  refine ⟨Set.range (fun k : ℕ => 2 ^ k),
    Set.infinite_range_of_injective (Nat.pow_right_injective (le_refl 2)), ?_, 0, ?_⟩
  · rintro ⟨k, hk⟩
    exact absurd hk (by positivity)
  · rintro m ⟨i, rfl⟩ n ⟨j, rfl⟩ _ h
    simp only at h ⊢
    have hji : j < i := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h
    have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hji
    rw [pow_succ] at this
    omega
