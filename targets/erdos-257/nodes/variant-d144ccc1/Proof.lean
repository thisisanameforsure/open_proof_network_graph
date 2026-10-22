import Mathlib
import Nodes.«variant-d144ccc1».Context

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

private lemma r2_weighted (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA : ∀ m ∈ A, ∀ n ∈ A, n < m → 2 * n ≤ m) (F : Finset ℕ) :
    (∀ a ∈ F, a ∈ A) → ∀ m ∈ A, (∀ a ∈ F, a < m) →
      (∑ a ∈ F, a) + (F.filter (fun a => 2 * a ∉ A)).card ≤ m := by
  induction F using Finset.induction_on_max with
  | empty => intro _ m _ _; simp
  | insert b s hlt ih =>
    intro hsA m hm hbm
    have hb : b ∈ A := hsA b (Finset.mem_insert_self b s)
    have hs : ∀ a ∈ s, a ∈ A := fun a ha => hsA a (Finset.mem_insert_of_mem ha)
    have hbs : b ∉ s := fun h => lt_irrefl b (hlt b h)
    have h1 := ih hs b hb hlt
    have hbm' : b < m := hbm b (Finset.mem_insert_self b s)
    have h2 := hA m hm b hb hbm'
    rw [Finset.sum_insert hbs, Finset.filter_insert]
    split_ifs with h2b
    · omega
    · have hbf : b ∉ s.filter (fun a => 2 * a ∉ A) := fun h => hbs (Finset.mem_filter.1 h).1
      rw [Finset.card_insert_of_notMem hbf]
      have hne : m ≠ 2 * b := fun h => h2b (h ▸ hm)
      omega

private lemma r2_hyp (A : Set ℕ) (hinf : A.Infinite) (h0 : 0 ∉ A)
    (hA : ∀ m ∈ A, ∀ n ∈ A, n < m → 2 * n ≤ m) :
    ∀ C : ℕ, ∃ m ∈ A, ∃ L : ℕ, 0 < L ∧ (∀ a ∈ A, a < m → 2 ^ a - 1 ∣ L) ∧ 2 ^ C * L ≤ 2 ^ m := by
  classical
  intro C
  have hpos : ∀ a ∈ A, 0 < 2 ^ a - 1 := by
    intro a ha
    have : a ≠ 0 := fun h => h0 (h ▸ ha)
    have := Nat.one_lt_two_pow this
    omega
  by_cases hND : {a | a ∈ A ∧ 2 * a ∉ A}.Infinite
  · obtain ⟨t, htND, htc⟩ := hND.exists_subset_card_eq (C + 1)
    have hne : t.Nonempty := by rw [← Finset.card_pos, htc]; omega
    set m := t.max' hne with hm
    have hmA : m ∈ A := (htND (Finset.max'_mem t hne)).1
    set F := (Finset.range m).filter (· ∈ A) with hF
    refine ⟨m, hmA, ∏ a ∈ F, (2 ^ a - 1), ?_, ?_, ?_⟩
    · exact Finset.prod_pos (fun a ha => hpos a (Finset.mem_filter.1 ha).2)
    · intro a ha ham
      exact Finset.dvd_prod_of_mem _ (by rw [hF, Finset.mem_filter, Finset.mem_range]; exact ⟨ham, ha⟩)
    · have hw := r2_weighted A hA F (fun a ha => (Finset.mem_filter.1 ha).2) m hmA
        (fun a ha => Finset.mem_range.1 (Finset.mem_filter.1 ha).1)
      have hsub : t.erase m ⊆ F.filter (fun a => 2 * a ∉ A) := by
        intro x hx
        rw [Finset.mem_erase] at hx
        have hxND := htND hx.2
        rw [Finset.mem_filter, hF, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨lt_of_le_of_ne (Finset.le_max' t x hx.2) hx.1, hxND.1⟩, hxND.2⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.max'_mem t hne), htc] at hcard
      have hL : ∏ a ∈ F, (2 ^ a - 1) ≤ 2 ^ (∑ a ∈ F, a) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod' (fun a _ => Nat.sub_le _ _)
      calc 2 ^ C * ∏ a ∈ F, (2 ^ a - 1) ≤ 2 ^ C * 2 ^ (∑ a ∈ F, a) := Nat.mul_le_mul_left _ hL
        _ = 2 ^ (C + ∑ a ∈ F, a) := by rw [pow_add]
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hfin : {a | a ∈ A ∧ 2 * a ∉ A}.Finite := Set.not_infinite.1 hND
    obtain ⟨b, hb⟩ := hfin.bddAbove
    have hn0 : ∀ a ∈ A, b + 1 ≤ a → 2 * a ∈ A := by
      intro a ha hab
      by_contra h
      have := hb ⟨ha, h⟩
      omega
    set F0 := (Finset.range (b + 1)).filter (· ∈ A) with hF0
    obtain ⟨n, hnA, hn⟩ := hinf.exists_gt (b + 1 + C + ∑ a ∈ F0, a)
    have hmA : 2 * n ∈ A := hn0 n hnA (by omega)
    refine ⟨2 * n, hmA, (∏ a ∈ F0, (2 ^ a - 1)) * (2 ^ n - 1), ?_, ?_, ?_⟩
    · exact Nat.mul_pos (Finset.prod_pos (fun a ha => hpos a (Finset.mem_filter.1 ha).2)) (hpos n hnA)
    · intro a ha ham
      by_cases hab : a < b + 1
      · apply Dvd.dvd.mul_right
        exact Finset.dvd_prod_of_mem _ (by rw [hF0, Finset.mem_filter, Finset.mem_range]; exact ⟨hab, ha⟩)
      · apply Dvd.dvd.mul_left
        apply Nat.pow_sub_one_dvd_pow_sub_one 2
        have han : a ≤ n := by
          by_contra h
          have := hA a ha n hnA (by omega)
          omega
        have ha1 : 1 ≤ a := by
          rcases Nat.eq_zero_or_pos a with h | h
          · exact absurd (h ▸ ha) h0
          · exact h
        have hdbl : ∀ j, a * 2 ^ j ∈ A := by
          intro j
          induction j with
          | zero => simpa using ha
          | succ j ihj =>
            have : a * 2 ^ (j + 1) = 2 * (a * 2 ^ j) := by ring
            rw [this]
            apply hn0 _ ihj
            have : a ≤ a * 2 ^ j := Nat.le_mul_of_pos_right a (by positivity)
            omega
        have hex : ∃ j, n < a * 2 ^ (j + 1) := by
          refine ⟨n, ?_⟩
          have h1 : n < 2 ^ (n + 1) := lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by omega))
          have h2 : 2 ^ (n + 1) ≤ a * 2 ^ (n + 1) := Nat.le_mul_of_pos_left _ ha1
          omega
        have hj := Nat.find_spec hex
        have hle : a * 2 ^ (Nat.find hex) ≤ n := by
          rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
          · rw [h]; simpa using han
          · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
            rw [Nat.sub_add_cancel h] at this
            omega
        have heq : a * 2 ^ (Nat.find hex) = n := by
          by_contra hne
          have hlt : a * 2 ^ (Nat.find hex) < n := lt_of_le_of_ne hle hne
          have := hA n hnA _ (hdbl (Nat.find hex)) hlt
          have e : a * 2 ^ (Nat.find hex + 1) = 2 * (a * 2 ^ (Nat.find hex)) := by ring
          omega
        exact ⟨2 ^ (Nat.find hex), heq.symm⟩
    · have hL : ∏ a ∈ F0, (2 ^ a - 1) ≤ 2 ^ (∑ a ∈ F0, a) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod' (fun a _ => Nat.sub_le _ _)
      calc 2 ^ C * ((∏ a ∈ F0, (2 ^ a - 1)) * (2 ^ n - 1))
          ≤ 2 ^ C * (2 ^ (∑ a ∈ F0, a) * 2 ^ n) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hL (Nat.sub_le _ _))
        _ = 2 ^ (C + ∑ a ∈ F0, a + n) := by rw [pow_add, pow_add, mul_assoc]
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)


private lemma r2_main (A : Set ℕ) (hinf : A.Infinite) (h0 : 0 ∉ A)
    (hA : ∀ m ∈ A, ∀ n ∈ A, n < m → 2 * n ≤ m) :
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) :=
  r2_liou A hinf h0 (r2_hyp A hinf h0 hA)

/-- Erdős 257 for sets that are eventually lacunary of ratio two: if `A` is an infinite set of
positive integers and, from some point `N` on, any two elements `n < m` of `A` satisfy `m ≥ 2n`,
then `∑_{n ∈ A} 1/(2^n - 1)` is irrational. Examples: `{2^k}`, `{2^k - 1}`, `{3^k}`, `{k!}`, any
infinite divisibility chain, and any finite set joined to one of these.

Proof by Liouville's criterion (`Opn.erdos_257_liouville_criterion`): finitely many terms change
the sum by a rational, so assume the ratio condition for all pairs. Call `a ∈ A` non-doubling
when `2a ∉ A`. If infinitely many elements are non-doubling, then for `m ∈ A` the elements below
`m` sum to at most `m` minus the number of non-doubling ones among them (induction on the
largest), so the product of their `2^a - 1` is at most `2^(m - C)` once `C` non-doubling elements
lie below `m`. If finitely many are, all below `b`, then above `b` the set is a doubling chain,
every element of `A` from `b` to `n` divides `n`, and with `m = 2n` the common denominator
`(∏_{a ∈ A, a ≤ b} (2^a - 1)) · (2^n - 1)` is at most `2^(m - C)` for `n` large. Either way the
positive tail from `m` on, below `4 · 2^(-m)`, cannot be a positive multiple of `1/(qL)`.

Covered in principle by Erdős (Math. Student 36, 1968), who proves irrationality for pairwise
coprime `A` with summable reciprocals and remarks that coprimality can be dropped; ratio
below two is beyond this elementary argument. -/
theorem Opn.erdos_257_eventually_ratio_two :
    ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
    (∃ N : ℕ, ∀ m ∈ A, ∀ n ∈ A, N ≤ n → n < m → 2 * n ≤ m) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  classical
  intro A hinf h0 ⟨N, hN⟩
  set B' := {a | a ∈ A ∧ N ≤ a} with hB'
  have hBinf : B'.Infinite := by
    have : B' = A \ {a | a < N} := by
      ext a; simp [hB', not_lt]
    rw [this]
    exact hinf.sdiff (Set.finite_lt_nat N)
  have hB0 : 0 ∉ B' := fun h => h0 h.1
  have hBr : ∀ m ∈ B', ∀ n ∈ B', n < m → 2 * n ≤ m :=
    fun m hm n hn hnm => hN m hm.1 n hn.1 hn.2 hnm
  have hirr := r2_main B' hBinf hB0 hBr
  set f : ℕ → ℝ := fun n => (1 : ℝ) / (2 ^ n - 1) with hf
  set F := (Finset.range N).filter (· ∈ A) with hF
  have hsA : Summable (A.indicator f) := lac_summable.indicator A
  have hsB : Summable (B'.indicator f) := lac_summable.indicator B'
  have hpt : ∀ n, A.indicator f n
      = (if n ∈ F then f n else 0) + B'.indicator f n := by
    intro n
    by_cases hn : n ∈ A <;> by_cases hnN : n < N
    · have : n ∉ B' := fun h => absurd h.2 (not_le.mpr hnN)
      simp [hF, hn, hnN, Set.indicator_of_notMem this]
    · have : n ∈ B' := ⟨hn, not_lt.mp hnN⟩
      simp [hF, hn, hnN, Set.indicator_of_mem this]
    · have : n ∉ B' := fun h => hn h.1
      simp [hF, hn, Set.indicator_of_notMem this]
    · have : n ∉ B' := fun h => hn h.1
      simp [hF, hn, Set.indicator_of_notMem this]
  have hsplit : ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)
      = (∑ a ∈ F, f a) + ∑' n : B', (1 : ℝ) / (2 ^ n.1 - 1) := by
    rw [tsum_subtype A f, tsum_subtype B' f]
    have hfin : Summable (fun n => if n ∈ F then f n else 0) :=
      summable_of_ne_finset_zero (s := F) (fun b hb => by simp [hb])
    rw [show (fun n => A.indicator f n) = fun n => (if n ∈ F then f n else 0) + B'.indicator f n
      from funext hpt]
    rw [Summable.tsum_add hfin hsB]
    congr 1
    rw [tsum_eq_sum (s := F) (fun b hb => by simp [hb])]
    exact Finset.sum_congr rfl (fun b hb => by simp [hb])
  have hq : (∑ a ∈ F, f a) = ((∑ a ∈ F, (1 : ℚ) / (2 ^ a - 1) : ℚ) : ℝ) := by
    push_cast; rfl
  rw [hsplit, hq]
  rintro ⟨r, hr⟩
  apply hirr
  refine ⟨r - ∑ a ∈ F, (1 : ℚ) / (2 ^ a - 1), ?_⟩
  rw [Rat.cast_sub, hr]
  ring
