/-! Non-vacuity witness (D-4 step 7): the statement's leading binders,
`∀ (n : ℕ) (color : ℕ → Fin n) (m : ℕ), …`, are inhabited — n = 1, the constant colouring, m = 0. -/

theorem witness : ∃ (n : ℕ) (color : ℕ → Fin n) (m : ℕ), True := ⟨1, fun _ => 0, 0, trivial⟩
