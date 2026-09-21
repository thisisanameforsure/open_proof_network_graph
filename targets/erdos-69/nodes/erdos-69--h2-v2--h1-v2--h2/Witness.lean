import Mathlib
import Nodes.«erdos-69--h2-v2--h1-v2--h2».Context

open scoped ArithmeticFunction.omega

theorem witness : ∃ M : ℕ, (∑' n : ℕ, (ω n : ℝ) / 2 ^ n = ∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1)) ∧
    (∀ N k : ℕ,
      ∑' j : ℕ, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1)
        = ∑ j ∈ Finset.range k, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1)
          + (∑' j : ℕ, (ω (N + k + 1 + j) : ℝ) / 2 ^ (j + 1)) / 2 ^ k) := by
  have h_lambert : ∑' n : ℕ, (ω n : ℝ) / 2 ^ n
      = ∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1) := by
    -- (a) the per-prime geometric series
    have hgeom : ∀ p : ℕ, 2 ≤ p →
        ∑' k : ℕ, ((1 / 2 : ℝ) ^ p) ^ (k + 1) = 1 / (2 ^ p - 1) := by
      intro p hp
      have hr0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p := by positivity
      have hr1 : (1 / 2 : ℝ) ^ p < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      have h2 : (1 : ℝ) < 2 ^ p := one_lt_pow₀ (by norm_num) (by omega)
      have h3 : (2 : ℝ) ^ p - 1 ≠ 0 := by linarith
      simp_rw [pow_succ]
      rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, one_div, inv_pow]
      field_simp
    -- (D) the multiples of a prime p, reindexed
    have hD : ∀ p : ℕ, p.Prime →
        ∑' n : ℕ, (if p ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0)
          = ∑' k : ℕ, ((1 / 2 : ℝ) ^ p) ^ (k + 1) := by
      intro p hp
      have hp1 : 1 ≤ p := hp.one_lt.le
      have hk : ∀ k : ℕ, p * k + (p - 1) + 1 = p * (k + 1) := by
        intro k
        rw [Nat.mul_succ, Nat.add_assoc, Nat.sub_add_cancel hp1]
      have hg : ∀ k : ℕ, ((1 / 2 : ℝ) ^ p) ^ (k + 1) ≠ 0 := fun k => by positivity
      refine tsum_eq_tsum_of_ne_zero_bij (fun k => p * k.1 + (p - 1)) ?_ ?_ ?_
      · intro k k' h
        have h' : p * k.1 + (p - 1) = p * k'.1 + (p - 1) := h
        exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hp.pos (Nat.add_right_cancel h'))
      · intro n hn
        have hn' := Function.mem_support.1 hn
        have hdvd : p ∣ n + 1 := by
          by_contra hnot
          exact hn' (if_neg hnot)
        obtain ⟨m, hm⟩ := hdvd
        rcases m with _ | k
        · omega
        · refine ⟨⟨k, hg k⟩, ?_⟩
          show p * k + (p - 1) = n
          rw [← hk k] at hm
          exact (Nat.add_right_cancel hm).symm
      · rintro ⟨k, -⟩
        show (if p ∣ p * k + (p - 1) + 1 then (1 / 2 : ℝ) ^ (p * k + (p - 1) + 1) else 0)
          = ((1 / 2 : ℝ) ^ p) ^ (k + 1)
        rw [hk k, if_pos (dvd_mul_right p (k + 1)), pow_mul]
    -- the column sums
    have hcol : ∀ p : Nat.Primes,
        ∑' n : ℕ, (if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0)
          = 1 / (2 ^ (p : ℕ) - 1) := by
      intro p
      rw [hD p p.2, hgeom p p.2.two_le]
    -- (R) each row is summable
    have hR : ∀ p : ℕ, Summable (fun n : ℕ => if p ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0) := by
      intro p
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (summable_geometric_of_lt_one (by norm_num) (by norm_num) : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n)
      · split_ifs <;> positivity
      · split_ifs
        · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
        · positivity
    -- (Cb), (Sc): the column sums are summable over the primes
    have hb : ∀ p : ℕ, p.Prime → (1 : ℝ) / (2 ^ p - 1) ≤ 2 * (1 / 2 : ℝ) ^ p := by
      intro p hp
      have h2p : (2 : ℝ) ≤ 2 ^ p := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp.one_lt.le
      have hpos : (0 : ℝ) < 2 ^ p / 2 := by positivity
      calc (1 : ℝ) / (2 ^ p - 1) ≤ 1 / (2 ^ p / 2) := one_div_le_one_div_of_le hpos (by linarith)
        _ = 2 * (1 / 2 : ℝ) ^ p := by rw [one_div_div, one_div_pow, mul_one_div]
    have hSc : Summable (fun p : Nat.Primes => (1 : ℝ) / (2 ^ (p : ℕ) - 1)) := by
      have hg : Summable (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
      refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hg.subtype (fun n => n.Prime))
      · have : (1 : ℝ) < 2 ^ (p : ℕ) := one_lt_pow₀ (by norm_num) p.2.ne_zero
        exact div_nonneg zero_le_one (by linarith)
      · exact hb p p.2
    -- (C) the double family is summable
    have hC : Summable (Function.uncurry
        (fun (p : Nat.Primes) (n : ℕ) => if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0)) := by
      have hnn : (0 : Nat.Primes × ℕ → ℝ) ≤ Function.uncurry
          (fun (p : Nat.Primes) (n : ℕ) => if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0) := by
        rintro ⟨p, n⟩
        show (0 : ℝ) ≤ (if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0)
        split_ifs <;> positivity
      refine (summable_prod_of_nonneg hnn).2 ⟨fun p => hR p, ?_⟩
      exact hSc.congr (fun p => (hcol p).symm)
    -- the swap
    have hswap : ∑' n : ℕ, ∑' p : Nat.Primes, (if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0)
        = ∑' p : Nat.Primes, ∑' n : ℕ, (if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0) :=
      hC.tsum_comm
    -- (B) the per-n collapse
    have hBgen : ∀ m : ℕ, m ≠ 0 → ∀ c : ℝ,
        ∑' p : Nat.Primes, (if (p : ℕ) ∣ m then c else 0) = (ω m : ℝ) * c := by
      intro m hm c
      let S : Finset Nat.Primes :=
        m.primeFactors.attach.map ⟨fun p => ⟨p.1, (Nat.mem_primeFactors.1 p.2).1⟩,
          fun p q h => Subtype.ext (Subtype.mk.inj h)⟩
      have hmem : ∀ p : Nat.Primes, p ∈ S ↔ (p : ℕ) ∈ m.primeFactors := by
        intro p
        constructor
        · intro hp
          obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hp
          exact q.2
        · intro hp
          exact Finset.mem_map.2 ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
      have hfin : ∀ p : Nat.Primes, p ∉ S → (if (p : ℕ) ∣ m then c else 0) = 0 := by
        intro p hp
        rw [if_neg]
        intro hdvd
        exact hp ((hmem p).2 (Nat.mem_primeFactors.2 ⟨p.2, hdvd, hm⟩))
      rw [tsum_eq_sum hfin]
      rw [Finset.sum_ite_of_true (fun p hp => (Nat.mem_primeFactors.1 ((hmem p).1 hp)).2.1)]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : S.card = m.primeFactors.card := by
        simp [S, Finset.card_map, Finset.card_attach]
      have hω : (m.primeFactors.card : ℝ) = ω m := by
        simp [ArithmeticFunction.cardDistinctFactors_apply]
        rfl
      rw [hcard, hω]
    have hB : ∀ n : ℕ,
        ∑' p : Nat.Primes, (if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0)
          = (ω (n + 1) : ℝ) / 2 ^ (n + 1) := by
      intro n
      rw [hBgen (n + 1) n.succ_ne_zero, one_div_pow, mul_one_div]
    -- the original series is summable (as in the partial)
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
    -- assembly
    calc ∑' n : ℕ, (ω n : ℝ) / 2 ^ n
        = ∑' n : ℕ, (ω (n + 1) : ℝ) / 2 ^ (n + 1) := by
          rw [hsum.tsum_eq_zero_add]
          simp
      _ = ∑' n : ℕ, ∑' p : Nat.Primes, (if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0) :=
          tsum_congr (fun n => (hB n).symm)
      _ = ∑' p : Nat.Primes, ∑' n : ℕ, (if (p : ℕ) ∣ n + 1 then (1 / 2 : ℝ) ^ (n + 1) else 0) := hswap
      _ = ∑' p : Nat.Primes, (1 : ℝ) / (2 ^ (p : ℕ) - 1) := tsum_congr hcol
  have omega_series_summable : Summable (fun n : ℕ => (ω n : ℝ) / 2 ^ n) := by
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
    refine Summable.of_nonneg_of_le (fun n => by positivity) hbound ?_
    exact (summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num [Real.norm_eq_abs])).add
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have tail_summable : ∀ (N : ℕ), Summable (fun j : ℕ => (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1)) := by
    intro N
    have hshift : Summable (fun j : ℕ => (ω (j + (N + 1)) : ℝ) / 2 ^ (j + (N + 1))) :=
      (summable_nat_add_iff (f := fun n : ℕ => (ω n : ℝ) / 2 ^ n) (N + 1)).2 omega_series_summable
    refine (hshift.mul_left ((2 : ℝ) ^ N)).congr (fun j => ?_)
    rw [show j + (N + 1) = N + 1 + j by omega]
    rw [show (2 : ℝ) ^ (N + 1 + j) = 2 ^ N * 2 ^ (j + 1) by rw [← pow_add]; congr 1; omega]
    field_simp
  have hpos : ∀ M : ℕ, 0 < ∑' j : ℕ, (ω (M + 1 + j) : ℝ) / 2 ^ (j + 1) := by
    intro M
    refine (tail_summable M).tsum_pos (fun j => by positivity) 1 ?_
    have h1 : 0 < ω (M + 1 + 1) := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]
      have : (M + 1 + 1).primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
      exact Finset.card_pos.2 this
    have : (0 : ℝ) < (ω (M + 1 + 1) : ℝ) := by exact_mod_cast h1
    positivity
  have tail_step : ∀ (N : ℕ), ∑' j : ℕ, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1)
      = (ω (N + 1) : ℝ) / 2 + (∑' j : ℕ, (ω (N + 1 + 1 + j) : ℝ) / 2 ^ (j + 1)) / 2 := by
    intro N
    rw [(tail_summable N).tsum_eq_zero_add, ← tsum_div_const]
    congr 1
    · simp
    · refine tsum_congr (fun j => ?_)
      rw [show N + 1 + (j + 1) = N + 1 + 1 + j by omega, pow_succ (2 : ℝ) (j + 1)]
      field_simp
  have hsplit : ∀ N k : ℕ,
    ∑' j : ℕ, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1)
      = ∑ j ∈ Finset.range k, (ω (N + 1 + j) : ℝ) / 2 ^ (j + 1)
        + (∑' j : ℕ, (ω (N + k + 1 + j) : ℝ) / 2 ^ (j + 1)) / 2 ^ k := by
    intro N k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, tail_step (N + k), Finset.sum_range_succ]
      rw [show N + (k + 1) = N + k + 1 by omega, show N + 1 + k = N + k + 1 by omega, pow_succ]
      field_simp
      ring
  have omega_le_logb : ∀ (n : ℕ), ∀ (hn : 1 ≤ n), (ω n : ℝ) ≤ Real.logb 2 n := by
    intro n hn
    have h1 : 2 ^ ω n ≤ n := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]
      calc 2 ^ n.primeFactorsList.dedup.length = 2 ^ n.primeFactors.card := rfl
        _ ≤ ∏ p ∈ n.primeFactors, p :=
            Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
        _ ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    have h2 : ((2 : ℝ) ^ ω n) ≤ (n : ℝ) := by exact_mod_cast h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.le_logb_iff_rpow_le (by norm_num) hn0, Real.rpow_natCast]
    exact h2
  have geo1 : HasSum (fun j : ℕ => (1 : ℝ) / 2 ^ (j + 1)) 1 := by
    have h' := (hasSum_geometric_two).mul_left (1 / 2 : ℝ)
    have hf : (fun j : ℕ => (1 : ℝ) / 2 ^ (j + 1)) = fun i : ℕ => 1 / 2 * (1 / 2 : ℝ) ^ i := by
      funext j
      rw [pow_succ, one_div_pow]
      field_simp
    have hv : (1 / 2 * 2 : ℝ) = 1 := by norm_num
    rw [hv] at h'
    rw [hf]
    exact h'
  have geo2 : HasSum (fun j : ℕ => (j : ℝ) / 2 ^ (j + 1)) 1 := by
    have h' := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ))
      (by norm_num [Real.norm_eq_abs])).mul_left (1 / 2 : ℝ)
    have hf : (fun j : ℕ => (j : ℝ) / 2 ^ (j + 1)) = fun i : ℕ => 1 / 2 * ((i : ℝ) * (1 / 2 : ℝ) ^ i) := by
      funext j
      rw [pow_succ, one_div_pow]
      field_simp
    have hv : (1 / 2 * (1 / 2 / (1 - 1 / 2) ^ 2) : ℝ) = 1 := by norm_num
    rw [hv] at h'
    rw [hf]
    exact h'
  have hbound : ∀ M : ℕ,
    ∑' j : ℕ, (ω (M + 1 + j) : ℝ) / 2 ^ (j + 1) ≤ Real.logb 2 ((M : ℝ) + 1) + 1 := by
    intro M
    have hL : 0 ≤ Real.logb 2 ((M : ℝ) + 1) := Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) M])
    have hterm : ∀ j : ℕ, (ω (M + 1 + j) : ℝ) / 2 ^ (j + 1)
        ≤ Real.logb 2 ((M : ℝ) + 1) * (1 / 2 ^ (j + 1)) + (j : ℝ) / 2 ^ (j + 1) := by
      intro j
      have h1 := omega_le_logb (M + 1 + j) (by omega)
      have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h2 : Real.logb 2 ((M + 1 + j : ℕ) : ℝ) ≤ Real.logb 2 (((M : ℝ) + 1) * ((j : ℝ) + 1)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) j]
      rw [Real.logb_mul hM.ne' hj.ne'] at h2
      have h3 : Real.logb 2 ((j : ℝ) + 1) ≤ (j : ℝ) := by
        rw [Real.logb_le_iff_le_rpow (by norm_num) hj, Real.rpow_natCast]
        have : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
        exact_mod_cast this
      have hp : (0 : ℝ) < 2 ^ (j + 1) := by positivity
      rw [mul_one_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hp.le
    have hs : HasSum (fun j : ℕ => Real.logb 2 ((M : ℝ) + 1) * (1 / 2 ^ (j + 1)) + (j : ℝ) / 2 ^ (j + 1))
        (Real.logb 2 ((M : ℝ) + 1) * 1 + 1) := (geo1.mul_left _).add geo2
    calc ∑' j : ℕ, (ω (M + 1 + j) : ℝ) / 2 ^ (j + 1)
        ≤ ∑' j : ℕ, (Real.logb 2 ((M : ℝ) + 1) * (1 / 2 ^ (j + 1)) + (j : ℝ) / 2 ^ (j + 1)) :=
          (tail_summable M).tsum_le_tsum hterm hs.summable
      _ = Real.logb 2 ((M : ℝ) + 1) + 1 := by rw [hs.tsum_eq, mul_one]
  exact ⟨0, h_lambert, hsplit⟩
