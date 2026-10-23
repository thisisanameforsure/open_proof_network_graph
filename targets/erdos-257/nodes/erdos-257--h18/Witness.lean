import Mathlib

theorem witness : ∃ A : Set ℕ, A.Infinite := ⟨Set.univ, Set.infinite_univ⟩
