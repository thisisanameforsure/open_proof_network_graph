import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (579124757 : ℕ) ≤ x ∧ x < (798128213 : ℕ) := ⟨579124757, by decide, by decide⟩
