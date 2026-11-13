import Mathlib
import Nodes.«variant-cce9b284--h5».Context

theorem witness : ∃ (r : ℕ → ℝ) (n : ℕ),
  r (0 : ℕ) = (1 : ℝ) / (2 : ℝ) ^ (20 : ℕ) ∧
    (∀ (k : ℕ),
        r (k + (1 : ℕ)) =
          if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ))
          else r k) ∧
      n ≤ (1091 : ℕ) :=
  ⟨fun n => Nat.rec (motive := fun _ => ℝ) ((1 : ℝ) / (2 : ℝ) ^ (20 : ℕ))
      (fun (k : ℕ) (acc : ℝ) => if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ acc
        then acc - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) else acc) n,
    0, rfl, fun _ => rfl, Nat.zero_le _⟩
