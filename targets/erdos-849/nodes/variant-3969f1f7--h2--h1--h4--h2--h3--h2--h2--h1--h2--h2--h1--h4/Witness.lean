import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (2325919 : ℕ) ≤ x ∧ x < (2442191 : ℕ) := ⟨2325919, by decide, by decide⟩
