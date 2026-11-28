/-! Non-vacuity witness (D-4 step 7): the statement's binders carry no hypothesis, so it suffices to exhibit a Latin square; the one of order 1, whose single cell holds 0, is one. -/

theorem witness : ∃ (n : ℕ) (L : LatinSquare n), True :=
  ⟨1, ⟨fun _ _ => 0, fun _ _ _ _ => Subsingleton.elim _ _, fun _ _ _ _ => Subsingleton.elim _ _⟩,
    trivial⟩
