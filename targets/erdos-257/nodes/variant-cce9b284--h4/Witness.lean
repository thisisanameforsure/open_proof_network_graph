import Mathlib
import Nodes.«variant-cce9b284--h4».Context

/-! The witness slot for a hole (D-29, F07-R6). Replace `sorry` with an instance
satisfying this statement's hypotheses; until then the node is blocked. -/

theorem witness : ∃ (r : ℕ → ℝ) (n : ℕ) (m : ℕ),
  r (0 : ℕ) = (1 : ℝ) / (2 : ℝ) ^ (20 : ℕ) ∧
    (∀ (k : ℕ),
        r (k + (1 : ℕ)) =
          if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ))
          else r k) ∧
      n < m := by
  sorry
