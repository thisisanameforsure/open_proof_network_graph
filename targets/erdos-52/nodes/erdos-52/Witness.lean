/-! Non-vacuity witness (D-4 step 7): the statement's leading binder and hypotheses,
`∀ ε : ℝ, 0 < ε → ε < 1 → …`, are satisfiable — ε = 1/2. -/

theorem witness : ∃ ε : ℝ, 0 < ε ∧ ε < 1 := ⟨1 / 2, by norm_num, by norm_num⟩
