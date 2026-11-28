/-! Non-vacuity witness (D-4 step 7): 0 is an idempotent of the group algebra ℚ[1], with ℚ and the trivial group lifted to the statement's universes. -/

theorem witness.{u_1, u_2} : ∃ (K : Type u_1) (inst : Field K) (G : Type u_2) (inst_1 : Group G)
    (a : MonoidAlgebra K G), IsIdempotentElem a :=
  ⟨ULift.{u_1} ℚ, inferInstance, PUnit.{u_2 + 1}, inferInstance, 0, IsIdempotentElem.zero⟩
