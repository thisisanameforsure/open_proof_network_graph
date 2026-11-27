import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (84655429 : ℕ) ≤ x ∧ x < (116593297 : ℕ) := ⟨84655429, by decide, by decide⟩
