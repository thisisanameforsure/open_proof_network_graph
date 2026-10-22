import Mathlib

theorem witness : ∃ (B : Set ℕ), B.Nonempty ∧ ∃ (p : ℕ), (0 : ℕ) < p ∧ ∀ (n : ℕ), n ∈ B ↔ n + p ∈ B :=
  ⟨Set.univ, Set.univ_nonempty, 1, Nat.one_pos, fun _ => by simp⟩
