import Nodes.«spec-689ac1ac».Context

theorem witness : ∃ (A : Set ℕ) (p : ℤ) (q : ℕ) (y : ℕ) (k : ℕ),
  (0 : ℕ) < q ∧
    ∑' (n : (↑A : Type)), (1 : ℝ) / ((2 : ℝ) ^ (↑n : ℕ) - (1 : ℝ)) = (↑p : ℝ) / (↑q : ℝ) ∧
      ∀ (i : ℕ), (1 : ℕ) ≤ i → i ≤ k → (2 : ℕ) ^ k ∣ {a : ℕ | a ∈ A ∧ a ∣ y + i}.ncard :=
  ⟨∅, 0, 1, 0, 0, one_pos, by rw [tsum_empty]; simp, fun i h1 h2 => absurd (h1.trans h2) (by norm_num)⟩
