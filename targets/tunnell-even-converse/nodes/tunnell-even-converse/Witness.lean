open CongruentNumber

/-! Non-vacuity witness (D-4 step 7): n = 6 is squarefree and even, and both C 6 and D 6 are empty (modulo 8, 6 = 8x² + 2y² + 16z² forces y² ≡ 3 mod 4), so 2·0 = 0. -/
theorem witness : ∃ (n : ℕ), Squarefree n ∧ Even n ∧
    2 * (CongruentNumber.C n).ncard = (CongruentNumber.D n).ncard := by
  have key : ∀ a b c : ZMod 8, (6 : ZMod 8) ≠ 8 * a ^ 2 + 2 * b ^ 2 + 64 * c ^ 2 ∧
      (6 : ZMod 8) ≠ 8 * a ^ 2 + 2 * b ^ 2 + 16 * c ^ 2 := by decide
  have hC : CongruentNumber.C 6 = ∅ := by
    ext ⟨x, y, z⟩
    simp only [CongruentNumber.C, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have := congrArg (Int.cast : ℤ → ZMod 8) h
    push_cast at this
    exact (key x y z).1 this
  have hD : CongruentNumber.D 6 = ∅ := by
    ext ⟨x, y, z⟩
    simp only [CongruentNumber.D, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have := congrArg (Int.cast : ℤ → ZMod 8) h
    push_cast at this
    exact (key x y z).2 this
  refine ⟨6, ?_, by decide, ?_⟩
  · have : (6 : ℕ) = 2 * 3 := rfl
    rw [this, Nat.squarefree_mul (by norm_num)]
    exact ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  · rw [hC, hD]; simp
