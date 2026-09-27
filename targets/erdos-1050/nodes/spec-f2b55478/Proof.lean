import Mathlib
import Nodes.«spec-f2b55478».Context

/-- erdos-1050, Borwein's route (annexes f593a93a8960 and 3ada4f0922d7 on erdos-1050--h1-v2):
the coefficient of x^m, for m > n, in Q_n(x) * f(x), where f(x) = sum_{k >= 1} x^k / (2^k - 1) and
Q_n(x) = sum_k (-1)^k 2^(k(k-1)/2) [n k]_2 [2n-k n]_2 x^k is the Pade denominator, equals
2^(n^2) (2;2)_n [m-n-1 n]_2 / prod_{j <= n} (2^(m-j) - 1). It vanishes for n < m <= 2n (the Pade
condition) and is positive for m > 2n, which makes the Pade remainder positive. Checked exactly for
n <= 15, m <= 3n + 29. -/
theorem erdos_1050_pade_remainder_coeff (n m : ℕ) (hnm : n < m) :
    ∑ j ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ j * (2 : ℚ) ^ (j * (j - 1) / 2) *
        (∏ i ∈ Finset.range j, ((2 : ℚ) ^ (n - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) *
        (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (2 * n - j - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) /
        ((2 : ℚ) ^ (m - j) - 1) =
      (2 : ℚ) ^ (n * n) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (i + 1) - 1)) *
        (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (m - n - 1 - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) /
        ∏ j ∈ Finset.range (n + 1), ((2 : ℚ) ^ (m - j) - 1) := by
  -- annex: fcdb7a3a0b0eac5a9cc9f17ce00a203d918c82203729e0d0a4c29795a1778f0d
  -- Step 4 of the annex (residue identity): c_j 2^j prod_(k != j) (2^j - 2^k) = N(2^j).
  have hres : ∀ j ∈ Finset.range (n + 1),
      ((-1 : ℚ) ^ j * (2 : ℚ) ^ (j * (j - 1) / 2) * (∏ i ∈ Finset.range j, ((2 : ℚ) ^ (n - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (2 * n - j - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1))) * (2 : ℚ) ^ j * ∏ k ∈ (Finset.range (n + 1)).erase j, ((2 : ℚ) ^ j - (2 : ℚ) ^ k) =
        ∏ i ∈ Finset.range n, ((2 : ℚ) ^ j - (2 : ℚ) ^ (n + 1 + i)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨r, rfl⟩ : ∃ r, n = j + r := ⟨n - j, by omega⟩
    have E1test : ∀ j r : ℕ, ∏ k ∈ (Finset.range (j + r + 1)).erase j, ((2:ℚ)^j - 2^k) =
        (∏ k ∈ Finset.range j, ((2:ℚ)^j - 2^k)) * ∏ x ∈ Finset.range r, ((2:ℚ)^j - 2^(j+1+x))  := by
        intro j r
        induction r with
        | zero =>
          simp [Finset.range_add_one]
        | succ r ih =>
          rw [show j + (r + 1) + 1 = (j + r + 1) + 1 by ring, Finset.range_add_one,
            Finset.erase_insert_of_ne (by omega), Finset.prod_insert (by simp), ih,
            Finset.prod_range_succ]
          rw [show j + 1 + r = j + r + 1 by ring]
          ring
    have E2test : ∀ j : ℕ, ∏ k ∈ Finset.range j, ((2:ℚ)^j - 2^k) =
        2 ^ (j * (j - 1) / 2) * ∏ i ∈ Finset.range j, ((2:ℚ)^(i+1) - 1)  := by
        intro j
        rw [← Finset.prod_range_reflect (fun i => (2:ℚ)^(i+1) - 1)]
        rw [show (2:ℚ) ^ (j * (j - 1) / 2) = ∏ k ∈ Finset.range j, (2:ℚ)^k by
          rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id], ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [show j - 1 - k + 1 = j - k by omega, mul_sub, ← pow_add, show k + (j - k) = j by omega]
        ring
    have E3test : ∀ j r : ℕ, ∏ x ∈ Finset.range r, ((2:ℚ)^j - 2^(j+1+x)) =
        (-1) ^ r * 2 ^ (j * r) * ∏ i ∈ Finset.range r, ((2:ℚ)^(i+1) - 1)  := by
        intro j r
        rw [show (-1:ℚ) ^ r * 2 ^ (j * r) = ∏ _x ∈ Finset.range r, (-(2:ℚ) ^ j) by
          rw [Finset.prod_const, Finset.card_range, pow_mul, ← mul_pow, neg_one_mul], ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        rw [show j + 1 + i = j + (i + 1) by ring, pow_add]
        ring
    have E4test : ∀ j r : ℕ, ∏ i ∈ Finset.range (j + r), ((2:ℚ)^j - 2^(j + r + 1 + i)) =
        (-1) ^ (j + r) * 2 ^ (j * (j + r)) * ∏ i ∈ Finset.range (j + r), ((2:ℚ)^(r + 1 + i) - 1)  := by
        intro j r
        rw [show (-1:ℚ) ^ (j + r) * 2 ^ (j * (j + r)) = ∏ _x ∈ Finset.range (j + r), (-(2:ℚ) ^ j) by
          rw [Finset.prod_const, Finset.card_range, pow_mul, ← mul_pow, neg_one_mul], ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        rw [show j + r + 1 + i = j + (r + 1 + i) by ring, pow_add]
        ring
    have hQ : ∀ t : ℕ, ∏ i ∈ Finset.range t, ((2 : ℚ) ^ (i + 1) - 1) ≠ 0 := by
      intro t
      rw [Finset.prod_ne_zero_iff]
      intro i _
      have : (1 : ℚ) < 2 ^ (i + 1) := one_lt_pow₀ (by norm_num) (by omega)
      linarith
    have hA : ∀ t : ℕ, ∏ i ∈ Finset.range t, ((2 : ℚ) ^ (r + 1 + i) - 1) ≠ 0 := by
      intro t
      rw [Finset.prod_ne_zero_iff]
      intro i _
      have : (1 : ℚ) < 2 ^ (r + 1 + i) := one_lt_pow₀ (by norm_num) (by omega)
      linarith
    have F1 : ∏ i ∈ Finset.range j, ((2 : ℚ) ^ (j + r - i) - 1) = ∏ i ∈ Finset.range j, ((2 : ℚ) ^ (r + 1 + i) - 1) := by
      rw [← Finset.prod_range_reflect (fun i => (2 : ℚ) ^ (r + 1 + i) - 1)]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show r + 1 + (j - 1 - i) = j + r - i by omega]
    have F2 : ∏ i ∈ Finset.range (j + r), ((2 : ℚ) ^ (2 * (j + r) - j - i) - 1) = ∏ i ∈ Finset.range (j + r), ((2 : ℚ) ^ (r + 1 + i) - 1) := by
      rw [← Finset.prod_range_reflect (fun i => (2 : ℚ) ^ (r + 1 + i) - 1)]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show r + 1 + (j + r - 1 - i) = 2 * (j + r) - j - i by omega]
    have F3 : ∏ i ∈ Finset.range (j + r), ((2 : ℚ) ^ (i + 1) - 1) = (∏ i ∈ Finset.range r, ((2 : ℚ) ^ (i + 1) - 1)) * ∏ i ∈ Finset.range j, ((2 : ℚ) ^ (r + 1 + i) - 1) := by
      rw [add_comm j r, Finset.prod_range_add]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [show r + i + 1 = r + 1 + i by ring]
    have hp : (2 : ℚ) ^ (j * (j - 1) / 2) * 2 ^ (j * (j - 1) / 2) * 2 ^ j * 2 ^ (j * r) = 2 ^ (j * (j + r)) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self j)
      rcases j with _ | s
      · simp
      · simp only [Nat.add_sub_cancel] at h2 ⊢
        zify at h2 ⊢
        linear_combination h2
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib, F1, F2, F3, E1test, E2test, E3test, E4test]
    have hQj := hQ j
    have hQr := hQ r
    have hAj := hA j
    rw [← hp, pow_add (-1 : ℚ)]
    field_simp
  -- Step 3 (partial fractions / Lagrange interpolation at the nodes 2^0..2^n), from step 4.
  have hpf : ∑ j ∈ Finset.range (n + 1), ((-1 : ℚ) ^ j * (2 : ℚ) ^ (j * (j - 1) / 2) * (∏ i ∈ Finset.range j, ((2 : ℚ) ^ (n - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (2 * n - j - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1))) * (2 : ℚ) ^ j / ((2 : ℚ) ^ m - (2 : ℚ) ^ j) =
      (∏ i ∈ Finset.range n, ((2 : ℚ) ^ m - (2 : ℚ) ^ (n + 1 + i))) / (∏ k ∈ Finset.range (n + 1), ((2 : ℚ) ^ m - (2 : ℚ) ^ k)) := by
    classical
    have hinj : Set.InjOn (fun k : ℕ => (2 : ℚ) ^ k) (Finset.range (n + 1) : Set ℕ) := by
      intro a _ b _ h
      exact (pow_right_inj₀ (by norm_num) (by norm_num)).mp h
    have hdeg : (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((2 : ℚ) ^ (n + 1 + i)))).degree <
        ((Finset.range (n + 1)).card : WithBot ℕ) := by
      rw [Polynomial.degree_prod]
      simp only [Polynomial.degree_X_sub_C, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.lt_succ_self n
    have key := Lagrange.eq_interpolate_of_eval_eq
      (fun j => (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((2 : ℚ) ^ (n + 1 + i)))).eval ((2 : ℚ) ^ j))
      hinj hdeg (fun i _ => rfl)
    have hev := congrArg (Polynomial.eval ((2 : ℚ) ^ m)) key
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at hev
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.basis, Polynomial.eval_prod,
      Lagrange.basisDivisor, Polynomial.eval_sub, Polynomial.eval_X] at hev
    rw [hev, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < m := by
      rw [Finset.mem_range] at hj
      omega
    have hxj : (2 : ℚ) ^ m - 2 ^ j ≠ 0 := by
      have : (2 : ℚ) ^ j < 2 ^ m := pow_lt_pow_right₀ (by norm_num) hj'
      linarith
    have hE1 : ∏ k ∈ (Finset.range (n + 1)).erase j, ((2 : ℚ) ^ m - 2 ^ k) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro k hk
      have hk' : k < m := by
        rw [Finset.mem_erase, Finset.mem_range] at hk
        omega
      have : (2 : ℚ) ^ k < 2 ^ m := pow_lt_pow_right₀ (by norm_num) hk'
      linarith
    have hE2 : ∏ k ∈ (Finset.range (n + 1)).erase j, ((2 : ℚ) ^ j - 2 ^ k) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro k hk
      rw [Finset.mem_erase] at hk
      intro h0
      exact hk.1 (hinj (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hk.2) (sub_eq_zero.mp h0)).symm
    rw [← Finset.mul_prod_erase _ _ hj, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← hres j hj]
    field_simp
  -- Step 1: each term c_j / (2^(m-j) - 1) = c_j 2^j / (2^m - 2^j), since j <= n < m.
  have hl : ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (2 : ℚ) ^ (j * (j - 1) / 2) * (∏ i ∈ Finset.range j, ((2 : ℚ) ^ (n - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (2 * n - j - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) / ((2 : ℚ) ^ (m - j) - 1) = ∑ j ∈ Finset.range (n + 1), ((-1 : ℚ) ^ j * (2 : ℚ) ^ (j * (j - 1) / 2) * (∏ i ∈ Finset.range j, ((2 : ℚ) ^ (n - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (2 * n - j - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1))) * (2 : ℚ) ^ j / ((2 : ℚ) ^ m - (2 : ℚ) ^ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < m := by
      rw [Finset.mem_range] at hj
      omega
    have h2 : (2 : ℚ) ^ m = 2 ^ (m - j) * 2 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj'.le]
    have hp : (2 : ℚ) ^ j ≠ 0 := by positivity
    rw [h2, show (2 : ℚ) ^ (m - j) * 2 ^ j - 2 ^ j = (2 ^ (m - j) - 1) * 2 ^ j by ring,
      mul_div_mul_right _ _ hp]
  -- Step 2: the right-hand side is N(2^m) / D(2^m).
  have hr : (2 : ℚ) ^ (n * n) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (i + 1) - 1)) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (m - n - 1 - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) / ∏ j ∈ Finset.range (n + 1), ((2 : ℚ) ^ (m - j) - 1) = (∏ i ∈ Finset.range n, ((2 : ℚ) ^ m - (2 : ℚ) ^ (n + 1 + i))) / (∏ k ∈ Finset.range (n + 1), ((2 : ℚ) ^ m - (2 : ℚ) ^ k)) := by
    have hB : ∏ i ∈ Finset.range n, ((2 : ℚ) ^ (i + 1) - 1) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      have : (1 : ℚ) < 2 ^ (i + 1) := one_lt_pow₀ (by norm_num) (by omega)
      linarith
    have key : (2 : ℚ) ^ (n * n) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (i + 1) - 1)) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (m - n - 1 - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1)) / ∏ j ∈ Finset.range (n + 1), ((2 : ℚ) ^ (m - j) - 1) = (2 : ℚ) ^ (n * n) * (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (m - n - 1 - i) - 1)) / (∏ j ∈ Finset.range (n + 1), ((2 : ℚ) ^ (m - j) - 1)) := by
      rw [Finset.prod_div_distrib]
      field_simp
    rcases Nat.lt_or_ge (2 * n) m with h | h
    · have hA : (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (m - n - 1 - i) - 1)) = (∏ i ∈ Finset.range n, ((2 : ℚ) ^ m - (2 : ℚ) ^ (n + 1 + i))) / 2 ^ (∑ i ∈ Finset.range n, (n + 1 + i)) := by
        rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have e : (2 : ℚ) ^ m = 2 ^ (m - n - 1 - i) * 2 ^ (n + 1 + i) := by
          rw [← pow_add]
          congr 1
          omega
        rw [e]
        field_simp
      have hD : (∏ j ∈ Finset.range (n + 1), ((2 : ℚ) ^ (m - j) - 1)) = (∏ k ∈ Finset.range (n + 1), ((2 : ℚ) ^ m - (2 : ℚ) ^ k)) / 2 ^ (∑ j ∈ Finset.range (n + 1), j) := by
        rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
        apply Finset.prod_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have e : (2 : ℚ) ^ m = 2 ^ (m - j) * 2 ^ j := by
          rw [← pow_add]
          congr 1
          omega
        rw [e]
        field_simp
      have hs : ∑ i ∈ Finset.range n, (n + 1 + i) = n * n + ∑ j ∈ Finset.range (n + 1), j := by
        rw [Finset.sum_range_succ, Finset.sum_add_distrib]
        simp
        ring
      have hDX : (∏ k ∈ Finset.range (n + 1), ((2 : ℚ) ^ m - (2 : ℚ) ^ k)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro k hk
        rw [Finset.mem_range] at hk
        have : (2 : ℚ) ^ k < 2 ^ m := pow_lt_pow_right₀ (by norm_num) (by omega)
        linarith
      rw [key, hA, hD, hs, pow_add]
      field_simp
    · have hz1 : (∏ i ∈ Finset.range n, ((2 : ℚ) ^ (m - n - 1 - i) - 1)) = 0 :=
        Finset.prod_eq_zero (i := m - n - 1) (by rw [Finset.mem_range]; omega)
          (by rw [show m - n - 1 - (m - n - 1) = 0 by omega]; norm_num)
      have hz2 : (∏ i ∈ Finset.range n, ((2 : ℚ) ^ m - (2 : ℚ) ^ (n + 1 + i))) = 0 :=
        Finset.prod_eq_zero (i := m - n - 1) (by rw [Finset.mem_range]; omega)
          (by rw [show n + 1 + (m - n - 1) = m by omega]; ring)
      rw [key, hz1, hz2]
      simp
  rw [hl, hr]
  exact hpf
