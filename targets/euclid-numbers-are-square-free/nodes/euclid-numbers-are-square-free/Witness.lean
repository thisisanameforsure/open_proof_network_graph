open EuclidNumbers

/-! Non-vacuity witness (D-4 step 7): the statement's only binder is `n : ℕ` with no hypotheses, so any natural number, here `0`, exhibits it. -/

theorem witness : ∃ (n : ℕ), True := ⟨0, trivial⟩
