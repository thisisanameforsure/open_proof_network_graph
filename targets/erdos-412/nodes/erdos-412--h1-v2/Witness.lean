import Mathlib

open ArithmeticFunction.sigma

theorem witness : ∃ (m : ℕ), (3 : ℕ) ≤ m ∧ ¬∃ (x : ℕ), (2 : ℕ) ≤ x ∧ x < m ∧
    ∃ (k : ℕ), (⇑(σ (1 : ℕ)) : ℕ → ℕ)^[k] x = m := by
  -- m = 5: orbits of σ₁ never decrease, and 2 → 3 → 4 → 7 skips 5
  have hle : ∀ n : ℕ, n ≤ σ 1 n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Nat.zero_le _
    · rw [ArithmeticFunction.sigma_one_apply]
      exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
        (Nat.mem_divisors_self n hn.ne')
  have h7 : ∀ k : ℕ, 7 ≤ (σ 1)^[k] 7 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (hle _)
  have s2 : σ 1 2 = 3 := by rw [ArithmeticFunction.sigma_one_apply]; decide
  have s3 : σ 1 3 = 4 := by rw [ArithmeticFunction.sigma_one_apply]; decide
  have s4 : σ 1 4 = 7 := by rw [ArithmeticFunction.sigma_one_apply]; decide
  have w4 : ∀ k : ℕ, (σ 1)^[k] 4 ≠ 5 := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [Function.iterate_succ_apply, s4]
      have := h7 k; omega
  have w3 : ∀ k : ℕ, (σ 1)^[k] 3 ≠ 5 := by
    intro k
    cases k with
    | zero => simp
    | succ k => rw [Function.iterate_succ_apply, s3]; exact w4 k
  have w2 : ∀ k : ℕ, (σ 1)^[k] 2 ≠ 5 := by
    intro k
    cases k with
    | zero => simp
    | succ k => rw [Function.iterate_succ_apply, s2]; exact w3 k
  refine ⟨5, by norm_num, ?_⟩
  rintro ⟨x, hx2, hx5, k, hk⟩
  interval_cases x
  · exact w2 k hk
  · exact w3 k hk
  · exact w4 k hk
