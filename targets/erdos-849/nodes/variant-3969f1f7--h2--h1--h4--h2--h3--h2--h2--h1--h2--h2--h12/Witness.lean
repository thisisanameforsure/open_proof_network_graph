import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (61487687 : ℕ) ≤ x ∧ x < (84655429 : ℕ) := ⟨61487687, by decide, by decide⟩
