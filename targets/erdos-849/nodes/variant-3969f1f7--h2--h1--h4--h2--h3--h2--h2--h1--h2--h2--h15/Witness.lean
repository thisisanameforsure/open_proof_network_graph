import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (160616597 : ℕ) ≤ x ∧ x < (221285089 : ℕ) := ⟨160616597, by decide, by decide⟩
