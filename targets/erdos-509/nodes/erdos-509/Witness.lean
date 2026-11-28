open Polynomial
open scoped Real
open Erdos509

/-! Non-vacuity witness (D-4 step 7): the polynomial `X` is monic and of degree one, so non-constant. -/

theorem witness : ∃ (f : ℂ[X]), f.Monic ∧ f.natDegree ≠ (0 : ℕ) :=
  ⟨Polynomial.X, Polynomial.monic_X, by simp⟩
