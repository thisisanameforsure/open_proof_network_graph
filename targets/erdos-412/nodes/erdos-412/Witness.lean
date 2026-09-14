/-! Non-vacuity witness (D-4 step 7): the statement's hypotheses, closed over the variables
they mention, are satisfiable. Written by the curator after the gate refused the drafted `True`
witness (F14-T15). -/

theorem witness : ∃ m n : ℕ, m ≥ 2 ∧ n ≥ 2 :=
  ⟨2, 2, le_refl 2, le_refl 2⟩
