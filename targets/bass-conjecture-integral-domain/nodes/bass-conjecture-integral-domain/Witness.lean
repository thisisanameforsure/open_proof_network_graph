open scoped Classical
open Arxiv.«math.0703548»

/-! Non-vacuity witness (D-4 step 7): the integers (lifted), the group of order two (lifted), a one-element index type, the zero matrix (an idempotent) and the generator of order two, whose order 2 is not a unit of ℤ. -/

theorem witness.{u_1, u_2, u_3} : ∃ (R : Type u_1) (inst : CommRing R) (G : Type u_2)
    (inst_1 : Group G) (n : Type u_3) (inst_2 : Fintype n)
    (A : Matrix n n (MonoidAlgebra R G)) (g : G),
    IsDomain R ∧ A * A = A ∧ ¬IsUnit ((orderOf g : ℕ) : R) := by
  have hdom : IsDomain (ULift.{u_1} ℤ) :=
    Function.Injective.isDomain (ULift.ringEquiv : ULift.{u_1} ℤ ≃+* ℤ).toRingHom
      ULift.ringEquiv.injective
  have ho : orderOf (ULift.up.{u_2} (Multiplicative.ofAdd (1 : ZMod 2))) = 2 := by
    let e : Multiplicative (ZMod 2) ≃* ULift.{u_2} (Multiplicative (ZMod 2)) := MulEquiv.ulift.symm
    have := orderOf_injective e.toMonoidHom (fun a b h => e.injective h)
      (Multiplicative.ofAdd (1 : ZMod 2))
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one] at this
    exact this
  refine ⟨ULift.{u_1} ℤ, inferInstance, ULift.{u_2} (Multiplicative (ZMod 2)), inferInstance,
    PUnit.{u_3 + 1}, inferInstance, 0, ULift.up (Multiplicative.ofAdd 1), hdom, by simp, ?_⟩
  rw [ho]
  intro h
  have h2 := h.map (ULift.ringEquiv : ULift.{u_1} ℤ ≃+* ℤ)
  simp only [map_natCast] at h2
  norm_num [Int.isUnit_iff] at h2
