import Mathlib
import Nodes.«variant-cce9b284--h3».Context

/-! The witness slot for a hole (D-29, F07-R6). Replace `sorry` with an instance
satisfying this statement's hypotheses; until then the node is blocked. -/

theorem witness : ∃ (L : ℕ) (p : ℕ) (r : ℕ → ℝ) (n : ℕ) (m : ℕ),
  r (0 : ℕ) = (↑p : ℝ) / (2 : ℝ) ^ L ∧
    (∀ (k : ℕ),
        r (k + (1 : ℕ)) =
          if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ))
          else r k) ∧
      L ≤ n ∧
        n < m ∧
          m + (10 : ℕ) ≤ (2 : ℕ) * n ∧
            r (n + (1 : ℕ)) < (1 : ℝ) / ((2 : ℝ) ^ (n + (1 : ℕ)) - (1 : ℝ)) ∧
              ∑' (i : ℕ), (1 : ℝ) / ((2 : ℝ) ^ (n + (2 : ℕ) + i) - (1 : ℝ)) < r (n + (1 : ℕ)) := by
  sorry
