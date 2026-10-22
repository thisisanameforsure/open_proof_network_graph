theorem witness : ∃ (A : Set ℕ), A.Infinite ∧
    ∃ p N : ℕ, 0 < p ∧ ∀ n, N ≤ n → (n ∈ A ↔ n + p ∈ A) :=
  ⟨Set.univ, Set.infinite_univ, 1, 0, Nat.one_pos, fun _ _ => by simp⟩
