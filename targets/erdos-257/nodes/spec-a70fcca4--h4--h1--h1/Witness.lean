import Mathlib

theorem witness : ∃ (r : ℕ → ℝ) (m : ℕ), r 0 = 1 / 2 ∧
    (∀ m, r (m + 1) = if (1 : ℝ) / (2 ^ m - 1) ≤ r m then r m - 1 / (2 ^ m - 1) else r m) ∧
    2 ≤ m ∧ r m < 1 / (2 ^ m - 1) :=
  ⟨fun m => Nat.rec (1 / 2 : ℝ)
      (fun k rk => if (1 : ℝ) / (2 ^ k - 1) ≤ rk then rk - 1 / (2 ^ k - 1) else rk) m,
    4, rfl, fun _ => rfl, by norm_num, by
      simp only [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, Nat.rec_add_one, Nat.rec_zero]
      norm_num⟩
