import Mathlib
import Nodes.«variant-f93b89d8».Context

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

private lemma gen_good (a b C : ℕ) (ha : 2 ≤ a) (hab : a < b) :
    ∃ J K : ℕ, C + a ^ J + b ^ K ≤ a ^ (J + 1) ∧ C + a ^ J + b ^ K ≤ b ^ (K + 1) := by
  by_cases h23 : a = 2 ∧ b = 3
  · obtain ⟨rfl, rfl⟩ := h23
    obtain ⟨J, k, h1, h2⟩ := u23_good C
    refine ⟨k, J, ?_, ?_⟩
    · rw [pow_succ]; omega
    · rw [pow_succ]; omega
  have hb4 : 4 ≤ b := by omega
  have hC1 : C < 4 ^ C := Nat.lt_pow_self (by norm_num)
  have hC2 : 4 ^ C ≤ b ^ C := Nat.pow_le_pow_left (by omega) C
  set X := b ^ (C + 1) with hXdef
  have hX : 4 * C + 4 ≤ X := by
    have : b ^ C * 4 ≤ b ^ C * b := Nat.mul_le_mul_left _ hb4
    rw [hXdef, pow_succ]; omega
  have hZdef : b ^ (C + 1 + 1) = X * b := pow_succ b (C + 1)
  set Z := b ^ (C + 1 + 1) with hZ
  have hZX : 4 * X ≤ Z := by
    rw [hZdef]; have := Nat.mul_le_mul_left X hb4; linarith
  have hQ : 4 * Z ≤ b ^ (C + 1 + 1 + 1) := by
    have e : b ^ (C + 1 + 1 + 1) = Z * b := by rw [hZ]; exact pow_succ b (C + 1 + 1)
    rw [e]; have := Nat.mul_le_mul_left Z hb4; linarith
  have hZ0 : Z ≠ 0 := by positivity
  set J := Nat.log a Z with hJ
  have hY1 : a ^ J ≤ Z := Nat.pow_log_le_self a hZ0
  have hY2 : Z < a ^ (J + 1) := Nat.lt_pow_succ_log_self (by omega) Z
  by_cases h : C + a ^ J + X ≤ Z
  · exact ⟨J, C + 1, by omega, by omega⟩
  · push_neg at h
    rcases Nat.lt_or_ge a 3 with ha2 | ha3
    · have ha2' : a = 2 := by omega
      subst ha2'
      refine ⟨J + 1, C + 1 + 1, ?_, ?_⟩
      · have e1 : 2 ^ (J + 1 + 1) = 2 ^ (J + 1) * 2 := pow_succ 2 (J + 1)
        have e2 : 2 ^ (J + 1) = 2 ^ J * 2 := pow_succ 2 J
        omega
      · have e2 : 2 ^ (J + 1) = 2 ^ J * 2 := pow_succ 2 J
        omega
    · refine ⟨J, C + 1 + 1, ?_, ?_⟩
      · have e1 : a ^ (J + 1) = a ^ J * a := pow_succ a J
        have : a ^ J * 3 ≤ a ^ J * a := Nat.mul_le_mul_left _ ha3
        omega
      · omega

/-- Erdős 257 for the union of the powers of two integer bases `2 ≤ a < b`:
`∑_{n ∈ {a^k} ∪ {b^k}} 1/(2^n - 1)` is irrational. This generalises
`Opn.erdos_257_powers_of_two_and_three` (the case `a = 2`, `b = 3`) to every pair of bases, with
no independence condition on `a` and `b`. Each part is a divisibility chain, so below `m` the
partial sum has the common denominator `(2^(a^J) - 1)(2^(b^K) - 1)`, where `a^J` and `b^K` are
the largest powers below `m`, and Liouville's criterion (`Opn.erdos_257_liouville_criterion`)
applies once `m - a^J - b^K` is unbounded along such `m`. Put `Z = b^(K+1)` and let `a^J` be the
largest power of `a` with `a^J ≤ Z`. Either `m = Z` has margin `Z - b^K - a^J ≥ C`, or `a^J` lies
within `b^K + C` of `Z`; in that case `m = a^(J+1)` (when `a ≥ 3`) or `m = 2^(J+2)` (when `a = 2`
and `b ≥ 4`) has margin at least `2 b^K - 2C`. Only the pair `(2, 3)` needs more: there the
Diophantine step `|2^y - 3·2^x| ≥ 2^x` from the proof of the two-and-three case is used. The
proof is elementary and complete. -/
theorem Opn.erdos_257_powers_of_two_bases :
    ∀ a b : ℕ, 2 ≤ a → a < b →
    Irrational (∑' n : ({n | ∃ k : ℕ, n = a ^ k} ∪ {n | ∃ k : ℕ, n = b ^ k} : Set ℕ),
      (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro a b ha hab
  set A : Set ℕ := {n | ∃ k : ℕ, n = a ^ k} ∪ {n | ∃ k : ℕ, n = b ^ k} with hA
  have hinf : A.Infinite := by
    apply Set.Infinite.mono Set.subset_union_left
    have : {n | ∃ k : ℕ, n = a ^ k} = Set.range (fun k : ℕ => a ^ k) := by
      ext n; simp [eq_comm]
    rw [this]
    exact Set.infinite_range_of_injective (Nat.pow_right_injective ha)
  have h0 : 0 ∉ A := by
    rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact absurd hk (pow_ne_zero k (by omega)).symm
    · exact absurd hk (pow_ne_zero k (by omega)).symm
  apply r2_liou A hinf h0
  intro C
  obtain ⟨J, K, hk1, hk2⟩ := gen_good a b C ha hab
  refine ⟨min (a ^ (J + 1)) (b ^ (K + 1)), ?_, (2 ^ (a ^ J) - 1) * (2 ^ (b ^ K) - 1), ?_, ?_, ?_⟩
  · rcases min_choice (a ^ (J + 1)) (b ^ (K + 1)) with h | h <;> rw [h]
    · exact Or.inl ⟨J + 1, rfl⟩
    · exact Or.inr ⟨K + 1, rfl⟩
  · apply Nat.mul_pos
    · have := Nat.one_lt_two_pow (pow_ne_zero J (by omega : a ≠ 0)); omega
    · have := Nat.one_lt_two_pow (pow_ne_zero K (by omega : b ≠ 0)); omega
  · rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) ham
    · apply Dvd.dvd.mul_right
      apply Nat.pow_sub_one_dvd_pow_sub_one 2
      have : a ^ i < a ^ (J + 1) := lt_of_lt_of_le ham (min_le_left _ _)
      have := (Nat.pow_lt_pow_iff_right (by omega : 1 < a)).1 this
      exact Nat.pow_dvd_pow a (by omega)
    · apply Dvd.dvd.mul_left
      apply Nat.pow_sub_one_dvd_pow_sub_one 2
      have : b ^ i < b ^ (K + 1) := lt_of_lt_of_le ham (min_le_right _ _)
      have := (Nat.pow_lt_pow_iff_right (by omega : 1 < b)).1 this
      exact Nat.pow_dvd_pow b (by omega)
  · calc 2 ^ C * ((2 ^ (a ^ J) - 1) * (2 ^ (b ^ K) - 1))
        ≤ 2 ^ C * (2 ^ (a ^ J) * 2 ^ (b ^ K)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ = 2 ^ (C + a ^ J + b ^ K) := by rw [pow_add, pow_add, mul_assoc]
      _ ≤ 2 ^ (min (a ^ (J + 1)) (b ^ (K + 1))) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [le_min_iff]
          exact ⟨hk1, hk2⟩
