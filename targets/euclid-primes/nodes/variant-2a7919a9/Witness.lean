/-! Non-vacuity witness (D-4 step 7): the statement has no hypothesis, so the witness is a list. -/

theorem witness : ∃ l : List Nat, True := ⟨[], trivial⟩
