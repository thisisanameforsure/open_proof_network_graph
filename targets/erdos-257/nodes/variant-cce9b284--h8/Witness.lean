import Mathlib
import Nodes.«variant-cce9b284--h8».Context

theorem witness : ∃ (A : Set ℕ), A.Finite ∧ ∀ a ∈ A, (1 : ℕ) ≤ a :=
  ⟨∅, Set.finite_empty, fun a ha => by simp at ha⟩
