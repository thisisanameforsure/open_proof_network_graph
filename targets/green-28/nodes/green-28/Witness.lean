open Green28

/-! Non-vacuity witness (D-4 step 7): X = Y = the point mass at 0; both have finite support and their independent sum is again the point mass at 0, which is uniform on the singleton {0}. -/

theorem witness : ∃ (X : PMF ℤ) (Y : PMF ℤ),
    X.support.Finite ∧ Y.support.Finite ∧ IsUniformOnSupport (indepSum X Y) := by
  have h : indepSum (PMF.pure 0) (PMF.pure 0) = PMF.pure 0 := by
    change ((PMF.pure (0 : ℤ)).bind fun x => (PMF.pure (0 : ℤ)).bind fun y => PMF.pure (x + y)) = _
    simp [PMF.pure_bind]
  refine ⟨PMF.pure 0, PMF.pure 0, by simp, by simp, {0}, Finset.singleton_nonempty 0, ?_⟩
  rw [h]
  ext z
  by_cases hz : z = 0 <;> simp [PMF.uniformOfFinset_apply, PMF.pure_apply, hz]
