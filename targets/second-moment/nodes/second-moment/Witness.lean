open Filter
open scoped Topology
open StableMarriage.Unbalanced

/-! Non-vacuity witness (D-4 step 7): the constant sequence d n = 1 is at least 1 and d n / n tends to 0. -/

theorem witness : ∃ (d : ℕ → ℕ), (∀ n, 1 ≤ d n) ∧ Tendsto (fun n ↦ (d n : ℝ) / n) atTop (𝓝 0) :=
  ⟨fun _ => 1, fun _ => le_refl 1, by simpa using tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)⟩
