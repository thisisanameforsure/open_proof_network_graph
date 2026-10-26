import Nodes.«spec-23b0fff0».Context

theorem witness : ∃ (A : Set ℕ) (p : ℤ) (q : ℕ) (j : ℕ),
  (0 : ℕ) < q ∧ ∑' (n : (↑A : Type)), (1 : ℝ) / ((2 : ℝ) ^ (↑n : ℕ) - (1 : ℝ)) = (↑p : ℝ) / (↑q : ℝ) :=
  ⟨∅, 0, 1, 0, one_pos, by rw [tsum_empty]; simp⟩
