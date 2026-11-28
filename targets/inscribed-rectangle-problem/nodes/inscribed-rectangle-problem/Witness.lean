open Topology ContDiff Manifold
open scoped EuclideanGeometry
open InscribedSquare

/-! Non-vacuity witness (D-4 step 7): the unit circle's inclusion into ℂ followed by the standard isometry ℂ ≃ ℝ² (the orthonormal basis 1, i) is an embedding, and r = 1. -/

theorem witness : ∃ (γ : Circle → ℝ²) (r : ℝ), IsEmbedding γ ∧ r > 0 :=
  ⟨fun z => Complex.orthonormalBasisOneI.repr (z : ℂ), 1,
    Complex.orthonormalBasisOneI.repr.toHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal,
    by norm_num⟩
