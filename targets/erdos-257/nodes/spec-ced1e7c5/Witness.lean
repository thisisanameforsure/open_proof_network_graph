import Nodes.«spec-ced1e7c5».Context

theorem witness : ∃ (A : Set ℕ) (p : ℤ) (q : ℕ) (y : ℕ) (k : ℕ),
  (0 : ℕ) < q ∧
    ∑' (n : (↑A : Type)), (1 : ℝ) / ((2 : ℝ) ^ (↑n : ℕ) - (1 : ℝ)) = (↑p : ℝ) / (↑q : ℝ) ∧
      (2 : ℕ) ^ k ∣ ∑ i ∈ Finset.range k, {a : ℕ | a ∈ A ∧ a ∣ y + i + (1 : ℕ)}.ncard * (2 : ℕ) ^ (k - (i + (1 : ℕ))) :=
  ⟨∅, 0, 1, 0, 0, one_pos, by rw [tsum_empty]; simp, by simp⟩
