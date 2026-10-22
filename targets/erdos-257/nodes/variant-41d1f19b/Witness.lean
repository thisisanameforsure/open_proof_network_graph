import Mathlib

theorem witness : ∃ (A : Set ℕ), A.Infinite ∧ (0 : ℕ) ∉ A ∧
    ∀ C : ℕ, ∃ m ∈ A, ∃ F : Finset ℕ, (∀ a, a ∈ F ↔ a ∈ A ∧ a < m) ∧ C + ∑ a ∈ F, a ≤ m := by
  have hsum : ∀ k : ℕ, k + ∑ j ∈ Finset.range k, 4 ^ j ≤ 4 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
      omega
  have hinj : Function.Injective (fun k : ℕ => 4 ^ k) := Nat.pow_right_injective (by norm_num)
  refine ⟨Set.range (fun k : ℕ => 4 ^ k), Set.infinite_range_of_injective hinj, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    exact absurd hk (by positivity)
  · intro C
    refine ⟨4 ^ C, ⟨C, rfl⟩, (Finset.range C).image (fun k : ℕ => 4 ^ k), ?_, ?_⟩
    · intro a
      simp only [Finset.mem_image, Finset.mem_range, Set.mem_range]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, rfl⟩, Nat.pow_lt_pow_right (by norm_num) hj⟩
      · rintro ⟨⟨j, rfl⟩, hj⟩
        exact ⟨j, (Nat.pow_lt_pow_iff_right (by norm_num)).1 hj, rfl⟩
    · rw [Finset.sum_image (fun x _ y _ h => hinj h)]
      exact hsum C
