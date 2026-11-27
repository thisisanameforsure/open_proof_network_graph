import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (17208887 : ℕ) ≤ x ∧ x < (23630771 : ℕ) := ⟨17208887, by decide, by decide⟩
