open Filter

/-! Non-vacuity witness (D-4 step 7): n k = (k+1)², strictly increasing, with n k / (k+1) = k + 1 → ∞, so the limsup is ⊤. -/

theorem witness : ∃ (n : ℕ → ℕ), StrictMono n ∧ atTop.limsup (fun k => (n k / k.succ : EReal)) = ⊤ := by
  refine ⟨fun k => (k + 1) ^ 2, fun a b h => ?_, ?_⟩
  · show (a + 1) ^ 2 < (b + 1) ^ 2
    exact Nat.pow_lt_pow_left (by omega) (by norm_num)
  · apply Filter.Tendsto.limsup_eq
    have hfun : (fun k : ℕ => ((((k + 1) ^ 2 : ℕ) : EReal) / ((k.succ : ℕ) : EReal)))
        = fun k : ℕ => (((k : ℝ) + 1 : ℝ) : EReal) := by
      funext k
      rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_coe_eq_natCast, ← EReal.coe_div]
      congr 1
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      rw [pow_two, mul_div_assoc, div_self hk, mul_one]
    show Tendsto (fun k : ℕ => ((((k + 1) ^ 2 : ℕ) : EReal) / ((k.succ : ℕ) : EReal))) atTop
      (nhds ⊤)
    rw [hfun, EReal.tendsto_nhds_top_iff_real]
    intro x
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop x] with k hk
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
