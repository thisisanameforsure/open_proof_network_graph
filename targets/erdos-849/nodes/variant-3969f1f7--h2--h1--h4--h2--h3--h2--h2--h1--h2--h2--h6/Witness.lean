import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (9167657 : ℕ) ≤ x ∧ x < (12548951 : ℕ) := ⟨9167657, by decide, by decide⟩
