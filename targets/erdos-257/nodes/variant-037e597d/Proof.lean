import Mathlib
import Nodes.«variant-037e597d».Context

private lemma lac_f_nonneg (n : ℕ) : 0 ≤ (1 : ℝ) / (2 ^ n - 1) := by
  apply div_nonneg zero_le_one
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  linarith

private lemma lac_f_le (n : ℕ) : (1 : ℝ) / (2 ^ n - 1) ≤ 2 * (1 / 2) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have h2 : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hpos : (0 : ℝ) < 2 ^ n - 1 := by linarith
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    rw [one_div_pow, div_le_iff₀ hpos]
    have e : (2 : ℝ) * (1 / 2 ^ n) * (2 ^ n - 1) = 2 - 2 / 2 ^ n := by
      field_simp
    have h3 : 2 / (2 : ℝ) ^ n ≤ 1 := (div_le_one hp).mpr h2
    linarith

private lemma lac_summable : Summable (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) :=
  Summable.of_nonneg_of_le lac_f_nonneg lac_f_le
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)

private lemma lac_tail_le (A : Set ℕ) (m : ℕ) :
    ∑' k : ℕ, A.indicator (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) (k + m) ≤ 4 * (1 / 2) ^ m := by
  classical
  have hrw : ∀ k : ℕ, 2 * (1 / 2 : ℝ) ^ (k + m) = (2 * (1 / 2) ^ m) * (1 / 2) ^ k := by
    intro k; rw [pow_add]; ring
  have hg : Summable (fun k : ℕ => 2 * (1 / 2 : ℝ) ^ (k + m)) := by
    simp_rw [hrw]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ k, A.indicator (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) (k + m)
      ≤ 2 * (1 / 2 : ℝ) ^ (k + m) := by
    intro k
    rw [Set.indicator_apply]
    split_ifs
    · exact lac_f_le _
    · positivity
  have hs : Summable (fun k : ℕ => A.indicator (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) (k + m)) :=
    Summable.of_nonneg_of_le (fun k => Set.indicator_nonneg (fun n _ => lac_f_nonneg n) _) hle hg
  calc _ ≤ ∑' k : ℕ, 2 * (1 / 2 : ℝ) ^ (k + m) := Summable.tsum_le_tsum hle hs hg
    _ = 4 * (1 / 2) ^ m := by
      simp_rw [hrw]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
      ring

private lemma liou_int (L : ℕ) (F : Finset ℕ) (hF : ∀ a ∈ F, 2 ^ a - 1 ∣ L)
    (hF0 : ∀ a ∈ F, a ≠ 0) :
    ∃ N : ℤ, (L : ℝ) * ∑ a ∈ F, (1 : ℝ) / (2 ^ a - 1) = N := by
  rw [Finset.mul_sum]
  have : ∀ a ∈ F, ∃ c : ℤ, (L : ℝ) * (1 / ((2 : ℝ) ^ a - 1)) = c := by
    intro a ha
    obtain ⟨c, hc⟩ := hF a ha
    refine ⟨c, ?_⟩
    have h1 : (1 : ℝ) < 2 ^ a := one_lt_pow₀ (by norm_num) (hF0 a ha)
    have h0 : (2 : ℝ) ^ a - 1 ≠ 0 := by linarith
    have hc' : (L : ℝ) = ((2 : ℝ) ^ a - 1) * c := by
      have h2 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      rw [hc]; push_cast [Nat.cast_sub h2]; ring
    rw [hc']; field_simp
    norm_cast
  choose c hc using this
  refine ⟨∑ a ∈ F.attach, c a.1 a.2, ?_⟩
  push_cast
  rw [← Finset.sum_attach F]
  exact Finset.sum_congr rfl (fun a _ => hc a.1 a.2)

private lemma r2_liou :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∀ C : ℕ, ∃ m ∈ A, ∃ L : ℕ, 0 < L ∧ (∀ a ∈ A, a < m → 2 ^ a - 1 ∣ L) ∧ 2 ^ C * L ≤ 2 ^ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  classical
  intro A _ h0 hA
  rintro ⟨r, hr⟩
  have hsum : Summable (A.indicator (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1))) :=
    lac_summable.indicator A
  have hrA : (r : ℝ) = ∑' n, A.indicator (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) n :=
    hr.trans (tsum_subtype A (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)))
  set q : ℕ := r.den with hq
  obtain ⟨m, hmA, L, hL0, hLdvd, hLm⟩ := hA (4 * q)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (h ▸ hmA) h0
    · exact h
  set F := (Finset.range m).filter (· ∈ A) with hF
  have hsplit := hsum.sum_add_tsum_nat_add m
  have hfin : ∑ i ∈ Finset.range m, A.indicator (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) i
      = ∑ a ∈ F, (1 : ℝ) / (2 ^ a - 1) := by
    rw [hF, Finset.sum_filter]
    simp [Set.indicator_apply]
  set T := ∑' i, A.indicator (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) (i + m) with hT
  have hTs : Summable (fun i => A.indicator (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) (i + m)) :=
    (summable_nat_add_iff m).mpr hsum
  have hTpos : 0 < T := by
    apply Summable.tsum_pos hTs (fun i => Set.indicator_nonneg (fun n _ => lac_f_nonneg n) _) 0
    rw [zero_add, Set.indicator_of_mem hmA]
    have : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) (by omega)
    apply div_pos one_pos; linarith
  have hTle : T ≤ 4 * (1 / 2) ^ m := lac_tail_le A m
  have hrT : (r : ℝ) = (∑ a ∈ F, (1 : ℝ) / (2 ^ a - 1)) + T := by
    rw [hrA, ← hsplit, hfin]
  obtain ⟨N, hN⟩ := liou_int L F
    (fun a ha => hLdvd a (Finset.mem_filter.1 ha).2 (Finset.mem_range.1 (Finset.mem_filter.1 ha).1))
    (fun a ha h => h0 (h ▸ (Finset.mem_filter.1 ha).2))
  have hPpos : (0 : ℝ) < L := by exact_mod_cast hL0
  have hqr : (r : ℝ) * q = r.num := by
    rw [hq]; exact_mod_cast Rat.mul_den_eq_num r
  have hZ : (q : ℝ) * L * T = ((L : ℤ) * r.num - q * N : ℤ) := by
    push_cast
    rw [← hN, ← hqr]
    have : T = r - ∑ a ∈ F, (1 : ℝ) / (2 ^ a - 1) := by linarith
    rw [this]; ring
  have hqpos : (0 : ℝ) < q := by
    rw [hq]; exact_mod_cast r.den_pos
  have hpos : (0 : ℝ) < (q : ℝ) * L * T := by positivity
  have hge : (1 : ℝ) ≤ (q : ℝ) * L * T := by
    rw [hZ] at hpos ⊢
    have : (0 : ℤ) < (L : ℤ) * r.num - q * N := by exact_mod_cast hpos
    exact_mod_cast this
  have hLm' : (2 : ℝ) ^ (4 * q) * L ≤ 2 ^ m := by exact_mod_cast hLm
  have hbig : (4 * q : ℝ) < 2 ^ (4 * q) := by
    have h1 : 4 * q < 2 ^ (4 * q) := Nat.lt_two_pow_self
    exact_mod_cast h1
  have h2m : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hupper : (q : ℝ) * L * T < 1 := by
    have hA1 : (q : ℝ) * L * T ≤ q * L * (4 * (1 / 2) ^ m) :=
      mul_le_mul_of_nonneg_left hTle (by positivity)
    have hA2 : (2 : ℝ) ^ (4 * q) * ((q : ℝ) * L * (4 * (1 / 2) ^ m))
        ≤ 4 * q * (2 ^ m * (1 / 2) ^ m) := by
      have := mul_le_mul_of_nonneg_right hLm' (by positivity : (0 : ℝ) ≤ 4 * q * (1 / 2) ^ m)
      nlinarith [this]
    rw [h2m, mul_one] at hA2
    have hpow : (0 : ℝ) < 2 ^ (4 * q) := by positivity
    have : (q : ℝ) * L * (4 * (1 / 2) ^ m) < 1 := by
      by_contra hc
      have hc2 := not_lt.mp hc
      nlinarith
    linarith
  linarith


private lemma u23_gap (a b : ℕ) : (2 : ℤ) ^ b ≤ |(2 : ℤ) ^ a - 3 * 2 ^ b| := by
  rcases le_or_gt a b with hab | hab
  · have : (2 : ℤ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hab
    have hp0 : (0 : ℤ) < 2 ^ b := by positivity
    rw [abs_of_neg (by linarith)]
    linarith
  · obtain ⟨d, rfl⟩ : ∃ d, a = b + d + 1 := ⟨a - b - 1, by omega⟩
    have e : (2 : ℤ) ^ (b + d + 1) - 3 * 2 ^ b = 2 ^ b * (2 * 2 ^ d - 3) := by ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ b)]
    have h1 : 1 ≤ |(2 : ℤ) * 2 ^ d - 3| := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; norm_num
      · have : (2 : ℤ) ≤ 2 ^ d := by
          calc (2 : ℤ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) h
        rw [abs_of_pos (by linarith)]; linarith
    have hp : (0 : ℤ) < 2 ^ b := by positivity
    nlinarith

private lemma u23_bad (C J : ℕ) (hJ : 1 ≤ J)
    (hbad : ¬ ∃ k : ℕ, 3 ^ J + C ≤ 2 ^ k ∧ 2 ^ k + C ≤ 2 * 3 ^ J) :
    ∃ x : ℕ, |(2 : ℤ) ^ x - 3 ^ J| < C := by
  set k := Nat.log 2 (3 ^ J) with hk
  have h1 : 2 ^ k ≤ 3 ^ J := Nat.pow_log_le_self 2 (by positivity)
  have h2 : 3 ^ J < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  by_cases hc : 3 ^ J + C ≤ 2 ^ (k + 1)
  · have hc2 : ¬ (2 ^ (k + 1) + C ≤ 2 * 3 ^ J) := fun h => hbad ⟨k + 1, hc, h⟩
    refine ⟨k, ?_⟩
    have : (3 : ℤ) ^ J - 2 ^ k < C := by
      have : 2 * 3 ^ J < 2 ^ (k + 1) + C := by omega
      have h' : (2 : ℤ) * 3 ^ J < 2 ^ (k + 1) + C := by exact_mod_cast this
      rw [pow_succ] at h'
      linarith
    have h0 : (2 : ℤ) ^ k ≤ 3 ^ J := by exact_mod_cast h1
    rw [abs_of_nonpos (by linarith)]
    linarith
  · refine ⟨k + 1, ?_⟩
    have h' : (2 : ℤ) ^ (k + 1) < 3 ^ J + C := by exact_mod_cast (not_le.mp hc)
    have h0 : (3 : ℤ) ^ J < 2 ^ (k + 1) := by exact_mod_cast h2
    rw [abs_of_pos (by linarith)]
    linarith

private lemma u23_good (C : ℕ) : ∃ J k : ℕ, 3 ^ J + C ≤ 2 ^ k ∧ 2 ^ k + C ≤ 2 * 3 ^ J := by
  have hJ : 5 * C + 1 ≤ 3 ^ (5 * C + 1) := (Nat.lt_pow_self (by norm_num)).le
  have hJ1 : 1 ≤ 5 * C + 1 := by omega
  set J := 5 * C + 1 with hJdef
  by_contra hno
  simp only [not_exists, not_and, not_le] at hno
  have hb1 : ¬ ∃ k : ℕ, 3 ^ J + C ≤ 2 ^ k ∧ 2 ^ k + C ≤ 2 * 3 ^ J :=
    fun ⟨k, h1, h2⟩ => absurd h2 (not_le.mpr (hno J k h1))
  have hb2 : ¬ ∃ k : ℕ, 3 ^ (J + 1) + C ≤ 2 ^ k ∧ 2 ^ k + C ≤ 2 * 3 ^ (J + 1) :=
    fun ⟨k, h1, h2⟩ => absurd h2 (not_le.mpr (hno (J + 1) k h1))
  obtain ⟨x, hx⟩ := u23_bad C J hJ1 hb1
  obtain ⟨y, hy⟩ := u23_bad C (J + 1) (by omega) hb2
  have hg := u23_gap y x
  have hJz : (5 * C + 1 : ℤ) ≤ 3 ^ J := by exact_mod_cast hJ
  have e : (2 : ℤ) ^ y - 3 * 2 ^ x = ((2 : ℤ) ^ y - 3 ^ (J + 1)) - 3 * ((2 : ℤ) ^ x - 3 ^ J) := by ring
  have h4 : |(2 : ℤ) ^ y - 3 * 2 ^ x| < 4 * C := by
    rw [e]
    calc |((2 : ℤ) ^ y - 3 ^ (J + 1)) - 3 * ((2 : ℤ) ^ x - 3 ^ J)|
        ≤ |(2 : ℤ) ^ y - 3 ^ (J + 1)| + |3 * ((2 : ℤ) ^ x - 3 ^ J)| := abs_sub _ _
      _ = |(2 : ℤ) ^ y - 3 ^ (J + 1)| + 3 * |(2 : ℤ) ^ x - 3 ^ J| := by
          rw [abs_mul]; norm_num
      _ < C + 3 * C := by linarith
      _ = 4 * C := by ring
  have h5 : (3 : ℤ) ^ J - C < 2 ^ x := by
    have := neg_abs_le ((2 : ℤ) ^ x - 3 ^ J)
    linarith
  linarith

/-- Erdős 257 for the powers of two together with the powers of three:
`∑_{n ∈ {2^k} ∪ {3^k}} 1/(2^n - 1)` is irrational. The set is not lacunary of ratio two
(`2^k < 3^j < 2^(k+1)` happens infinitely often), so `Opn.erdos_257_eventually_ratio_two` does
not apply, but Liouville's criterion (`Opn.erdos_257_liouville_criterion`) does. Each part is a
divisibility chain, so below `m` the common denominator of the partial sum is
`(2^(2^k) - 1)(2^(3^J) - 1)`, with `2^k` and `3^J` the largest powers below `m`; taking
`m = min(2^(k+1), 3^(J+1))`, it suffices that some power `2^k` lies in `[3^J + C, 2·3^J - C]`.
If that failed for both `J` and `J + 1`, both `3^J` and `3^(J+1)` would lie within `C` of a power
of two, `2^x` and `2^y`, and then `|2^y - 3·2^x| < 4C`. But `|2^y - 3·2^x| ≥ 2^x`, because
`2^d ≠ 3`. That is impossible once `3^J ≥ 5C + 1`. The reciprocals of the set are
summable, so the result is covered in principle by Erdős's remark (Math. Student 36, 1968) that
coprimality can be dropped from his 1968 theorem; the proof here is elementary and complete. -/
theorem Opn.erdos_257_powers_of_two_and_three :
    Irrational (∑' n : ({n | ∃ k : ℕ, n = 2 ^ k} ∪ {n | ∃ k : ℕ, n = 3 ^ k} : Set ℕ),
      (1 : ℝ) / (2 ^ n.1 - 1)) := by
  set A : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k} ∪ {n | ∃ k : ℕ, n = 3 ^ k} with hA
  have hinf : A.Infinite := by
    apply Set.Infinite.mono Set.subset_union_left
    have : {n | ∃ k : ℕ, n = 2 ^ k} = Set.range (fun k : ℕ => 2 ^ k) := by
      ext n; simp [eq_comm]
    rw [this]
    exact Set.infinite_range_of_injective (Nat.pow_right_injective (le_refl 2))
  have h0 : 0 ∉ A := by
    rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> exact absurd hk (by positivity)
  apply r2_liou A hinf h0
  intro C
  obtain ⟨J, k, hk1, hk2⟩ := u23_good C
  refine ⟨min (2 ^ (k + 1)) (3 ^ (J + 1)), ?_, (2 ^ (2 ^ k) - 1) * (2 ^ (3 ^ J) - 1), ?_, ?_, ?_⟩
  · rcases min_choice (2 ^ (k + 1)) (3 ^ (J + 1)) with h | h <;> rw [h]
    · exact Or.inl ⟨k + 1, rfl⟩
    · exact Or.inr ⟨J + 1, rfl⟩
  · apply Nat.mul_pos
    · have := Nat.one_lt_two_pow (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)); omega
    · have := Nat.one_lt_two_pow (pow_ne_zero J (by norm_num : (3 : ℕ) ≠ 0)); omega
  · rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩) ham
    · apply Dvd.dvd.mul_right
      apply Nat.pow_sub_one_dvd_pow_sub_one 2
      have : 2 ^ i < 2 ^ (k + 1) := lt_of_lt_of_le ham (min_le_left _ _)
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 this
      exact Nat.pow_dvd_pow 2 (by omega)
    · apply Dvd.dvd.mul_left
      apply Nat.pow_sub_one_dvd_pow_sub_one 2
      have : 3 ^ i < 3 ^ (J + 1) := lt_of_lt_of_le ham (min_le_right _ _)
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 this
      exact Nat.pow_dvd_pow 3 (by omega)
  · calc 2 ^ C * ((2 ^ (2 ^ k) - 1) * (2 ^ (3 ^ J) - 1))
        ≤ 2 ^ C * (2 ^ (2 ^ k) * 2 ^ (3 ^ J)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ = 2 ^ (C + 2 ^ k + 3 ^ J) := by rw [pow_add, pow_add, mul_assoc]
      _ ≤ 2 ^ (min (2 ^ (k + 1)) (3 ^ (J + 1))) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [le_min_iff, pow_succ, pow_succ]
          constructor <;> omega
