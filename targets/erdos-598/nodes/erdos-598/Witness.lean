open Cardinal
open Erdos598

/-! Non-vacuity witness (D-4 step 7): `ULift ℕ` is an infinite type in every universe. -/
theorem witness.{u_1} : ∃ (m : Type u_1), Infinite m := ⟨ULift ℕ, inferInstance⟩
