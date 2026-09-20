import Defs.IsPrime
import Mathlib.Tactic

theorem witness : ∃ (l : List ℕ), ∀ x ∈ l, x ≤ l.sum := ⟨[], by simp⟩
