import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (23630771 : ℕ) ≤ x ∧ x < (32479943 : ℕ) := ⟨23630771, by decide, by decide⟩
