import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (12548951 : ℕ) ≤ x ∧ x < (17208887 : ℕ) := ⟨12548951, by decide, by decide⟩
