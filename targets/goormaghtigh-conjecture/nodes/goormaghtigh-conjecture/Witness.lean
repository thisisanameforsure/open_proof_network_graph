open Goormaghtigh

/-! Non-vacuity witness (D-4 step 7): 31 = 1 + 2 + 4 + 8 + 16 = 1 + 5 + 25 is a repunit in bases 2 and 5, so a Goormaghtigh number. -/
theorem witness : ∃ (N : ℕ), IsGoormaghtighNumber N :=
  ⟨31, 2, 5, 5, 3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by simp [repunit, Finset.sum_range_succ], by simp [repunit, Finset.sum_range_succ]⟩
