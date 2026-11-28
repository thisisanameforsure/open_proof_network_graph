open scoped Polynomial
open PierceBirkhoff

/-! Non-vacuity witness (D-4 step 7): the zero function on ℝ^0 is piecewise polynomial, with the single closed semi-algebraic piece `Set.univ` and the polynomial 0. -/
theorem witness : ∃ (n : ℕ) (f : (Fin n → ℝ) → ℝ), IsPiecewiseMvPolynomial f :=
  ⟨0, fun _ => 0, Unit, fun _ => Set.univ, fun _ => 0, inferInstance,
    fun _ => isClosed_univ,
    fun _ => ⟨Unit, fun _ => ∅, fun _ => ∅, inferInstance, by ext x; simp⟩,
    Set.iUnion_eq_univ_iff.mpr fun _ => ⟨(), trivial⟩, fun _ _ _ => by simp⟩
