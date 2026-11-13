import Mathlib
import Nodes.«variant-cce9b284--h7».Context

theorem witness : ∃ (x : ℝ) (r : ℕ → ℝ),
  (0 : ℝ) ≤ x ∧
    x ≤ (1 : ℝ) ∧
      r (0 : ℕ) = x ∧
        (∀ (k : ℕ),
            r (k + (1 : ℕ)) =
              if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ))
              else r k) ∧
          ∀ (n : ℕ),
            ¬(r (n + (1 : ℕ)) < (1 : ℝ) / ((2 : ℝ) ^ (n + (1 : ℕ)) - (1 : ℝ)) ∧
                ∑' (i : ℕ), (1 : ℝ) / ((2 : ℝ) ^ (n + (2 : ℕ) + i) - (1 : ℝ)) < r (n + (1 : ℕ))) := by
  have hpos : ∀ k : ℕ, 1 ≤ k → (0 : ℝ) < (1 : ℝ) / ((2 : ℝ) ^ k - 1) := by
    intro k hk
    have h2 : (1 : ℝ) < (2 : ℝ) ^ k := one_lt_pow₀ (by norm_num) (by omega)
    exact div_pos one_pos (by linarith)
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ (1 : ℝ) / ((2 : ℝ) ^ k - 1) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · exact (hpos k hk).le
  refine ⟨0, fun _ => 0, le_rfl, zero_le_one, rfl, ?_, ?_⟩
  · intro k
    have : ¬ ((1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ (0 : ℝ)) := by
      rintro ⟨hk, h⟩
      exact absurd h (not_le.mpr (hpos k hk))
    simp only [this, if_false]
  · intro n ⟨_, h⟩
    have : (0 : ℝ) ≤ ∑' (i : ℕ), (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + i) - 1) :=
      tsum_nonneg (fun i => hnn _)
    linarith
