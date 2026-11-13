import Mathlib
import Nodes.«variant-cce9b284--h4».Context

theorem witness : ∃ (r : ℕ → ℝ) (n : ℕ) (m : ℕ),
  r (0 : ℕ) = (1 : ℝ) / (2 : ℝ) ^ (20 : ℕ) ∧
    (∀ (k : ℕ),
        r (k + (1 : ℕ)) =
          if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ))
          else r k) ∧
      n < m :=
  ⟨fun n => Nat.rec ((1 : ℝ) / (2 : ℝ) ^ (20 : ℕ))
      (fun k acc => if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ acc
        then acc - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) else acc) n,
    0, 1, rfl, fun _ => rfl, Nat.zero_lt_one⟩
