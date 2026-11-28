open Topology ContDiff Manifold
open scoped EuclideanGeometry
open InscribedSquare

/-! Non-vacuity witness (D-4 step 7): the unit circle itself, sent into the Euclidean plane by the real-linear isometry ℂ ≃ ℝ² of the basis (1, i). -/
theorem witness : ∃ (γ : Circle → ℝ²), IsEmbedding γ :=
  ⟨fun z => Complex.orthonormalBasisOneI.repr (z : ℂ),
    Complex.orthonormalBasisOneI.repr.toHomeomorph.isEmbedding.comp ⟨⟨rfl⟩, Circle.coe_injective⟩⟩
