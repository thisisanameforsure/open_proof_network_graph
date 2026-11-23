/-! Non-vacuity witness (D-4 step 7): the statement opens with binders that carry no
hypothesis, so the expected witness type is their closure over `True`, inhabited by
`default`. -/

theorem witness : ∃ (a : ℕ), True := ⟨default, trivial⟩
