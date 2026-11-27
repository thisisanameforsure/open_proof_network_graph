import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (116593297 : ℕ) ≤ x ∧ x < (160616597 : ℕ) := ⟨116593297, by decide, by decide⟩
