import Mathlib

open Nat

theorem witness : ∃ (x : ℕ), (4929469 : ℕ) ≤ x ∧ x < (6713221 : ℕ) := ⟨4929469, by decide, by decide⟩
