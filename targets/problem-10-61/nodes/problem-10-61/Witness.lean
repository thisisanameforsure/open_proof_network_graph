open Bugeaud61

/-! Non-vacuity witness (D-4 step 7): α = 3 is a Pisot number above 2 (minimal polynomial X - 3), and 0 = cantorPoint 3 (all digits false) lies in C(3). -/

theorem witness : ∃ (α : ℝ) (ξ : ℝ), IsPisot α ∧ (2 : ℝ) < α ∧ ξ ∈ pisotCantorSet α := by
  refine ⟨3, cantorPoint 3 (fun _ => false), ⟨by norm_num, ?_, ?_⟩, by norm_num, ⟨_, rfl⟩⟩
  · simpa using isIntegral_algebraMap (R := ℤ) (A := ℝ) (x := 3)
  · intro z hz hne
    have hm : minpoly ℚ (3 : ℝ) = Polynomial.X - Polynomial.C (3 : ℚ) := by
      simpa using minpoly.eq_X_sub_C ℝ (3 : ℚ)
    rw [hm, Polynomial.aroots_X_sub_C] at hz
    simp at hz hne
    exact absurd hz hne
