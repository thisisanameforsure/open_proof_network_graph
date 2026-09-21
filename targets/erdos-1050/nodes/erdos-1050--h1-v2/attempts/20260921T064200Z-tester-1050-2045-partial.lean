import Mathlib

/-! Hole `borwein` of a merged partial proof, as a node (D-12 #5, D-29).
Revised statement (D-8): the parent assembly's own `have borwein` type, with the binder types and
the real-number ascriptions the gate-written statement had dropped. -/

theorem erdos_1050__h1 : ∃ a b : ℕ → ℤ,
    (∀ n : ℕ, (b n : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3)) - a n ≠ 0) ∧
    Filter.Tendsto
      (fun n : ℕ => (b n : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3)) - a n)
      Filter.atTop (nhds 0) := by
  -- annex: 64a620c1871c74b895ed548471f33a563f6b78f76de69ee1c3852308605c5122
  -- Dirichlet: an irrational real has integer approximants b n * T - a n, nonzero and tending to 0.
  have approximants_of_irrational (T : ℝ) (hT : Irrational T) : ∃ a b : ℕ → ℤ,
    (∀ n : ℕ, (b n : ℝ) * T - a n ≠ 0) ∧
    Filter.Tendsto (fun n : ℕ => (b n : ℝ) * T - a n) Filter.atTop (nhds 0) := by
    have h : ∀ n : ℕ, ∃ j k : ℤ, 0 < k ∧ k ≤ ((n + 1 : ℕ) : ℤ) ∧
        |(k : ℝ) * T - j| ≤ 1 / (((n + 1 : ℕ) : ℝ) + 1) :=
      fun n => Real.exists_int_int_abs_mul_sub_le T (Nat.succ_pos n)
    choose a b hb0 _ hab using h
    refine ⟨a, b, fun n h0 => ?_, ?_⟩
    · have hbne : (b n : ℝ) ≠ 0 := by exact_mod_cast (hb0 n).ne'
      have hq : (((a n : ℚ) / (b n : ℚ) : ℚ) : ℝ) = T := by
        push_cast
        field_simp
        linarith
      exact hT ⟨_, hq⟩
    · refine squeeze_zero_norm (a := fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) (fun n => ?_) ?_
      · rw [Real.norm_eq_abs]; exact hab n
      · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h2 := (Filter.tendsto_add_atTop_iff_nat 1).mpr this
        simpa using h2
  -- The whole of Borwein's theorem for the tail T (q = 2, r = -3), in its plain form.
  have hT : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3)) := by
    sorry
  exact approximants_of_irrational _ hT
