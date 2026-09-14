/-! Non-vacuity witness (D-4 step 7): the statement's hypotheses, closed over the variables
they mention, are satisfiable. Written by the curator after the gate refused the drafted `True`
witness (F14-T15). -/

theorem witness : ∃ k : ℕ, k ≥ 2 :=
  ⟨2, le_refl 2⟩
