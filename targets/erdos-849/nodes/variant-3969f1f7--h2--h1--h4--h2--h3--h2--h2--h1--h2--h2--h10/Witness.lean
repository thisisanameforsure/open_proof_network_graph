import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (32479943 : ℕ) ≤ x ∧ x < (44677583 : ℕ) := ⟨32479943, by decide, by decide⟩
