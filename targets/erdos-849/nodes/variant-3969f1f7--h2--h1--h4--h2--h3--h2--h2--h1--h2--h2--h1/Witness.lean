import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (2010760 : ℕ) ≤ x ∧ x < (2694739 : ℕ) := ⟨2010760, by decide, by decide⟩
