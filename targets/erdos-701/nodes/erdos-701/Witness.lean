open Cardinal

/-! Non-vacuity witness (D-4 step 7): the one-point type with the empty family, which is a lower set. -/

theorem witness : ∃ (X : Type) (inst : Fintype X) (F : Set (Set X)), Nonempty X ∧ IsLowerSet F :=
  ⟨Unit, inferInstance, ∅, inferInstance, isLowerSet_empty⟩
