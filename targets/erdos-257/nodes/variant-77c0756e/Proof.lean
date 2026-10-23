import Mathlib
import Nodes.«variant-77c0756e».Context

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


private lemma ch_gt (x : ℕ → ℕ) (h0 : 0 < x 0) (h3 : ∀ j, 3 * x j ≤ x (j + 1)) :
    ∀ j, j < x j := by
  intro j
  induction j with
  | zero => exact h0
  | succ j ih => have := h3 j; omega

private lemma ch_mono (x : ℕ → ℕ) (h0 : 0 < x 0) (h3 : ∀ j, 3 * x j ≤ x (j + 1)) :
    StrictMono x := by
  apply strictMono_nat_of_lt_succ
  intro j
  have := h3 j; have := ch_gt x h0 h3 j; omega

private lemma ch_dvd (x : ℕ → ℕ) (hd : ∀ j, x j ∣ x (j + 1)) :
    ∀ i j, i ≤ j → x i ∣ x j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact dvd_rfl
  | succ j _ ih => exact ih.trans (hd j)

private lemma ch_good (x y : ℕ → ℕ) (hx0 : 0 < x 0) (hy0 : 0 < y 0)
    (hx3 : ∀ j, 3 * x j ≤ x (j + 1)) (hy3 : ∀ j, 3 * y j ≤ y (j + 1)) (C : ℕ) :
    ∃ J K : ℕ, C + x J + y K ≤ x (J + 1) ∧ C + x J + y K ≤ y (K + 1) := by
  classical
  set K := 3 * C + x 0 with hK
  have hX : K < y K := ch_gt y hy0 hy3 K
  have hZX : 3 * y K ≤ y (K + 1) := hy3 K
  have hQ : 3 * y (K + 1) ≤ y (K + 1 + 1) := hy3 (K + 1)
  have hex : ∃ j, y (K + 1) < x j := ⟨y (K + 1), ch_gt x hx0 hx3 _⟩
  set J1 := Nat.find hex with hJ1
  have hJ1spec : y (K + 1) < x J1 := Nat.find_spec hex
  have hJ1pos : J1 ≠ 0 := by
    intro h
    rw [h] at hJ1spec
    omega
  obtain ⟨J, hJ⟩ : ∃ J, J1 = J + 1 := ⟨J1 - 1, by omega⟩
  have hY1 : x J ≤ y (K + 1) := by
    have := Nat.find_min hex (show J < J1 by omega)
    omega
  have hY2 : y (K + 1) < x (J + 1) := hJ ▸ hJ1spec
  by_cases h : C + x J + y K ≤ y (K + 1)
  · exact ⟨J, K, by omega, by omega⟩
  · push_neg at h
    have hP := hx3 J
    exact ⟨J, K + 1, by omega, by omega⟩

/-- Erdős 257 for the union of two fast divisibility chains. Let `x` and `y` be sequences of
positive integers in which each term divides the next and is at most a third of it
(`x j ∣ x (j+1)` and `3 x j ≤ x (j+1)`, the same for `y`). Then
`∑_{n ∈ range x ∪ range y} 1/(2^n - 1)` is irrational. Examples: the powers of any two bases
`a, b ≥ 3`, or `{3^k} ∪ {(3k)!}`, or `{2·3^k} ∪ {5^k}`. Such a union need not be lacunary of
ratio two, and the elements below an element need not sum to less than it, so neither
`Opn.erdos_257_eventually_ratio_two` nor `Opn.erdos_257_long_gaps` applies. The proof uses
Liouville's criterion (`Opn.erdos_257_liouville_criterion`): below `m` the partial sum has the
common denominator `(2^(x J) - 1)(2^(y K) - 1)`, with `x J` and `y K` the largest chain elements
below `m`. Put `Z = y (K+1)` and let `x J` be the largest `x`-element with `x J ≤ Z`. Either
`m = Z` leaves margin `Z - y K - x J ≥ C`, or `x J > Z - y K - C`, and then
`m = min (x (J+1)) (y (K+2))` leaves margin at least `C`, because `x (J+1) ≥ 3 x J` and
`Z ≥ 3 y K`. The proof is elementary and complete. -/
theorem Opn.erdos_257_two_chains :
    ∀ x y : ℕ → ℕ, 0 < x 0 → 0 < y 0 →
    (∀ j, x j ∣ x (j + 1)) → (∀ j, y j ∣ y (j + 1)) →
    (∀ j, 3 * x j ≤ x (j + 1)) → (∀ j, 3 * y j ≤ y (j + 1)) →
    Irrational (∑' n : (Set.range x ∪ Set.range y : Set ℕ), (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro x y hx0 hy0 hxd hyd hx3 hy3
  set A : Set ℕ := Set.range x ∪ Set.range y with hA
  have hinf : A.Infinite :=
    Set.Infinite.mono Set.subset_union_left
      (Set.infinite_range_of_injective (ch_mono x hx0 hx3).injective)
  have h0 : 0 ∉ A := by
    rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · have := ch_gt x hx0 hx3 k; omega
    · have := ch_gt y hy0 hy3 k; omega
  apply r2_liou A hinf h0
  intro C
  obtain ⟨J, K, hk1, hk2⟩ := ch_good x y hx0 hy0 hx3 hy3 C
  have hxJ := ch_gt x hx0 hx3 J
  have hyK := ch_gt y hy0 hy3 K
  refine ⟨min (x (J + 1)) (y (K + 1)), ?_, (2 ^ (x J) - 1) * (2 ^ (y K) - 1), ?_, ?_, ?_⟩
  · rcases min_choice (x (J + 1)) (y (K + 1)) with h | h <;> rw [h]
    · exact Or.inl ⟨J + 1, rfl⟩
    · exact Or.inr ⟨K + 1, rfl⟩
  · apply Nat.mul_pos
    · have := Nat.one_lt_two_pow (show x J ≠ 0 by omega); omega
    · have := Nat.one_lt_two_pow (show y K ≠ 0 by omega); omega
  · rintro n (⟨i, rfl⟩ | ⟨i, rfl⟩) ham
    · apply Dvd.dvd.mul_right
      apply Nat.pow_sub_one_dvd_pow_sub_one 2
      have : x i < x (J + 1) := lt_of_lt_of_le ham (min_le_left _ _)
      have := (ch_mono x hx0 hx3).lt_iff_lt.1 this
      exact ch_dvd x hxd i J (by omega)
    · apply Dvd.dvd.mul_left
      apply Nat.pow_sub_one_dvd_pow_sub_one 2
      have : y i < y (K + 1) := lt_of_lt_of_le ham (min_le_right _ _)
      have := (ch_mono y hy0 hy3).lt_iff_lt.1 this
      exact ch_dvd y hyd i K (by omega)
  · calc 2 ^ C * ((2 ^ (x J) - 1) * (2 ^ (y K) - 1))
        ≤ 2 ^ C * (2 ^ (x J) * 2 ^ (y K)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ = 2 ^ (C + x J + y K) := by rw [pow_add, pow_add, mul_assoc]
      _ ≤ 2 ^ (min (x (J + 1)) (y (K + 1))) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [le_min_iff]
          exact ⟨hk1, hk2⟩
