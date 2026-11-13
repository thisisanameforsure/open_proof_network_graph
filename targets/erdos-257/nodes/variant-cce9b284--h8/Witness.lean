import Mathlib
import Nodes.«variant-cce9b284--h8».Context

/-! The witness slot for a hole (D-29, F07-R6). Replace `sorry` with an instance
satisfying this statement's hypotheses; until then the node is blocked. -/

theorem witness : ∃ (A : Set ℕ), A.Finite ∧ ∀ a ∈ A, (1 : ℕ) ≤ a := by
  sorry
