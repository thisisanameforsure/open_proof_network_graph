import Mathlib

open scoped ArithmeticFunction.omega

theorem erdos_69__h2 : (∑' n : ℕ, (ω n : ℝ) / 2 ^ n
      = ∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1)) →
    Irrational (∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1)) := by
  intro h_lambert
  -- Hole B (Erdős 1948): for every b ≥ 1 there is an N whose rescaled tail
  -- ∑_j ω(N+1+j)/2^(j+1) = 2^N · ∑_{n > N} ω(n)/2^n, times b, is not an integer — the choice
  -- of N by the Chinese remainder theorem that controls ω(N+1), ω(N+2), … .
  have hB : ∀ b : ℕ, 0 < b → ∃ N : ℕ, ∀ z : ℤ,
      (b : ℝ) * ∑' j : ℕ, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1) ≠ z := sorry
  -- Integrality (proved): if the series is the rational q, every rescaled tail times q.den is an
  -- integer, namely 2^N · q.num − ∑_{n ≤ N} q.den · ω(n) · 2^(N−n).
  have hA : ∀ q : ℚ, (q : ℝ) = ∑' n : ℕ, (ω n : ℝ) / 2 ^ n → ∀ N : ℕ,
      ∃ z : ℤ, (q.den : ℝ) * ∑' j : ℕ, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1) = z := by
    intro q hq N
    have hbound : ∀ n : ℕ,
        (ω n : ℝ) / 2 ^ n ≤ (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n := by
      intro n
      have h1 : ω n ≤ n + 1 := by
        rw [ArithmeticFunction.cardDistinctFactors_apply]
        calc n.primeFactorsList.dedup.length = n.primeFactors.card := rfl
          _ ≤ (Finset.range (n + 1)).card :=
              Finset.card_le_card (fun p hp =>
                Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors hp)))
          _ = n + 1 := Finset.card_range _
      have h2 : (ω n : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h1
      have h4 : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
      rw [pow_one, one_div, inv_pow, div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_right h2 h4]
    have hsum : Summable (fun n : ℕ => (ω n : ℝ) / 2 ^ n) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) hbound ?_
      exact (summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num [Real.norm_eq_abs])).add
        (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    have h2N : (2 : ℝ) ^ N ≠ 0 := by positivity
    -- the tail as 2^N times (the sum minus its first N+1 terms)
    have htail : ∑' j : ℕ, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1)
        = 2 ^ N * (∑' n : ℕ, (ω n : ℝ) / 2 ^ n - ∑ n ∈ Finset.range (N + 1), (ω n : ℝ) / 2 ^ n) := by
      have h := hsum.sum_add_tsum_nat_add (N + 1)
      have h2 : ∑' i : ℕ, (ω (i + (N + 1)) : ℝ) / 2 ^ (i + (N + 1))
          = (∑' j : ℕ, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1)) / 2 ^ N := by
        rw [← tsum_div_const]
        refine tsum_congr (fun j => ?_)
        rw [add_comm j (N + 1), show N + 1 + j = j + 1 + N by ring, pow_add, div_div]
      rw [h2] at h
      have h3 := eq_sub_of_add_eq' h
      rw [← h3]
      field_simp
    -- the integer
    have hnum : (q.den : ℝ) * (q : ℝ) = q.num := by
      have := congrArg (Rat.cast : ℚ → ℝ) (Rat.mul_den_eq_num q)
      push_cast at this
      linarith
    have hS : (q.den : ℝ) * ∑' n : ℕ, (ω n : ℝ) / 2 ^ n = q.num := by rw [← hq]; exact hnum
    have hA : ∑ n ∈ Finset.range (N + 1), (q.den : ℝ) * (ω n : ℝ) * 2 ^ (N - n)
        = 2 ^ N * ((q.den : ℝ) * ∑ n ∈ Finset.range (N + 1), (ω n : ℝ) / 2 ^ n) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hn' : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
      rw [pow_sub₀ (2 : ℝ) two_ne_zero hn']
      field_simp
    refine ⟨2 ^ N * q.num - ∑ n ∈ Finset.range (N + 1), (q.den : ℤ) * ω n * 2 ^ (N - n), ?_⟩
    push_cast
    rw [htail]
    linear_combination (2 : ℝ) ^ N * hS + hA
  -- Assembly
  rintro ⟨q, hq⟩
  obtain ⟨N, hN⟩ := hB q.den q.den_pos
  obtain ⟨z, hz⟩ := hA q (hq.trans h_lambert.symm) N
  exact hN z hz
