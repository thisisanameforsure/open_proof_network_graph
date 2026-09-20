import Defs.IsPrime
import Mathlib.Tactic

theorem witness : ∃ (l : List ℕ) (x : ℕ), x ∈ l := ⟨[0], 0, by simp⟩
