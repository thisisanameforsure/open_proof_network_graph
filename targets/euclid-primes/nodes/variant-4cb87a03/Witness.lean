/-! Non-vacuity witness (D-4 step 7): the statement has no hypothesis, so the witness is a
number, as on the root. -/

theorem witness : ∃ n : Nat, True := ⟨0, trivial⟩
