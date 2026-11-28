open Finset

/-! Non-vacuity witness (D-4 step 7): the binders carry no hypothesis; the trivial group `PUnit` with the empty set. -/
theorem witness.{u_1} : ∃ (G : Type u_1) (inst : AddCommGroup G) (inst : Fintype G)
    (inst : DecidableEq G) (A : Finset G), True :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, ∅, trivial⟩
