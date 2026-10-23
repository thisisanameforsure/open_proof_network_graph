import Mathlib
import Nodes.«variant-90827f46».Context

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



private lemma lu_geo_sum : ∀ T (S : Finset ℕ), (∀ a ∈ S, a ≤ T) →
    (∀ a ∈ S, ∀ b ∈ S, a < b → 2 * a ≤ b) → ∑ a ∈ S, a ≤ 2 * T := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
  intro S hT hR
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · set M := S.max' hne with hM
    have hMS : M ∈ S := S.max'_mem hne
    have hMT : M ≤ T := hT M hMS
    have hsplit : ∑ a ∈ S, a = M + ∑ a ∈ S.erase M, a := (Finset.add_sum_erase S _ hMS).symm
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · have hz : ∀ a ∈ S, a = 0 := fun a ha => by
        have hle : a ≤ M := S.le_max' a ha
        omega
      rw [Finset.sum_eq_zero hz]
      omega
    · have hsub : ∀ a ∈ S.erase M, a ≤ M / 2 := by
        intro a ha
        have haS := Finset.mem_of_mem_erase ha
        have hne' := Finset.ne_of_mem_erase ha
        have hle : a ≤ M := S.le_max' a haS
        have hlt : a < M := lt_of_le_of_ne hle hne'
        have := hR a haS M hMS hlt
        omega
      have hrest := ih (M / 2) (by omega) (S.erase M) hsub
        (fun a ha b hb hab => hR a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab)
      omega

private lemma lu_gt (c : ℕ → ℕ) (R : ℕ) (hR2 : 2 ≤ R) (h0 : 0 < c 0)
    (hR : ∀ j, R * c j ≤ c (j + 1)) : ∀ j, j < c j := by
  intro j
  induction j with
  | zero => exact h0
  | succ j ih =>
    have h1 := hR j
    have h2 : 2 * c j ≤ R * c j := Nat.mul_le_mul_right _ hR2
    omega

private lemma lu_mono (c : ℕ → ℕ) (R : ℕ) (hR2 : 2 ≤ R) (h0 : 0 < c 0)
    (hR : ∀ j, R * c j ≤ c (j + 1)) : StrictMono c := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h1 := hR j
  have h2 : 2 * c j ≤ R * c j := Nat.mul_le_mul_right _ hR2
  have := lu_gt c R hR2 h0 hR j
  omega

private lemma lu_ratio (c : ℕ → ℕ) (R : ℕ) (hR2 : 2 ≤ R) (h0 : 0 < c 0)
    (hR : ∀ j, R * c j ≤ c (j + 1)) : ∀ i j, i < j → R * c i ≤ c j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact hR i
  | succ j _ ih =>
    have : c j < c (j + 1) := (lu_mono c R hR2 h0 hR).lt_iff_lt.2 (by omega)
    omega

private lemma lu_window (r : ℕ) (c : Fin r → ℕ → ℕ) (R : ℕ) (hR2 : 2 ≤ R)
    (hRq : (2 * r + 1) ^ (r + 1) ≤ R) (h0 : ∀ i, 0 < c i 0)
    (hR : ∀ i j, R * c i j ≤ c i (j + 1)) (T : ℕ) :
    ∃ k ≤ r, ∀ i j, c i j ≤ (2 * r + 1) ^ k * T ∨ (2 * r + 1) ^ (k + 1) * T < c i j := by
  classical
  by_contra hcon
  push_neg at hcon
  have hk : ∀ k : Fin (r + 1), ∃ i : Fin r, ∃ j,
      (2 * r + 1) ^ (k : ℕ) * T < c i j ∧ c i j ≤ (2 * r + 1) ^ ((k : ℕ) + 1) * T :=
    fun k => hcon k (Nat.lt_succ_iff.mp k.2)
  choose f g hfg using hk
  obtain ⟨k1, k2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have h1 := hfg k1
  have h2 := hfg k2
  rw [heq] at h1
  set i := f k2
  have hk1 : (k1 : ℕ) ≤ r := Nat.lt_succ_iff.mp k1.2
  have hk2 : (k2 : ℕ) ≤ r := Nat.lt_succ_iff.mp k2.2
  have hq : 1 ≤ 2 * r + 1 := by omega
  have hTlow : ∀ k : ℕ, T ≤ (2 * r + 1) ^ k * T := fun k => by
    have := Nat.mul_le_mul_right T (Nat.one_le_pow k (2 * r + 1) (by omega))
    simpa using this
  have hThigh : ∀ k : ℕ, k ≤ r → (2 * r + 1) ^ (k + 1) * T ≤ R * T := fun k hk =>
    Nat.mul_le_mul_right T ((Nat.pow_le_pow_right hq (by omega)).trans hRq)
  rcases lt_trichotomy (g k1) (g k2) with hlt | heqj | hgt
  · have hr := lu_ratio (c i) R hR2 (h0 i) (hR i) _ _ hlt
    have a1 := hTlow k1
    have a2 := hThigh k2 hk2
    have a3 : R * (T + 1) ≤ R * c i (g k1) := Nat.mul_le_mul_left R (by omega)
    rw [Nat.mul_add, Nat.mul_one] at a3
    omega
  · rw [heqj] at h1
    have hne' : (k1 : ℕ) ≠ k2 := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · have := Nat.mul_le_mul_right T (Nat.pow_le_pow_right hq (show (k1 : ℕ) + 1 ≤ k2 by omega))
      omega
    · have := Nat.mul_le_mul_right T (Nat.pow_le_pow_right hq (show (k2 : ℕ) + 1 ≤ k1 by omega))
      omega
  · have hr := lu_ratio (c i) R hR2 (h0 i) (hR i) _ _ hgt
    have a1 := hTlow k2
    have a2 := hThigh k1 hk1
    have a3 : R * (T + 1) ≤ R * c i (g k2) := Nat.mul_le_mul_left R (by omega)
    rw [Nat.mul_add, Nat.mul_one] at a3
    omega

/-- Erdős 257 for a union of finitely many lacunary sequences. Let `c 0, …, c (r-1)` be `r ≥ 1`
sequences of positive integers, each growing by a factor of at least `(2r+1)^(r+1)` from one
term to the next (no divisibility and no relation between the sequences is assumed). Then
`∑_{n ∈ A} 1/(2^n - 1)` is irrational for `A` the union of their ranges. For `r = 1` the
factor is 9 (a case `Opn.erdos_257_eventually_ratio_two` already covers); for three sequences
it is `7^4 = 2401`, met for instance by `n ↦ 2401^n`, `n ↦ 3·2401^n` and
`n ↦ (n + 1)·2401^n`, the last not a divisibility chain. The union need not be lacunary of ratio two,
so `Opn.erdos_257_eventually_ratio_two` does not apply, and the sequences need not be
divisibility chains, as `Opn.erdos_257_two_chains` requires. Proof: by pigeonhole over the
`r + 1` windows `(q^k T, q^(k+1) T]`, `q = 2r+1`, `k = 0, …, r`, one window contains no
element of `A`, because two elements of one sequence in `(T, q^(r+1) T]` would contradict its
growth. The least element `m` of `A` above `q^k T` then exceeds `(2r+1) q^k T`, while the
elements of each sequence below `m` are at most `q^k T` and sum to at most twice that. So `m`
exceeds the sum of all smaller elements of `A` by at least `T`, and Liouville's criterion
(`Opn.erdos_257_liouville_criterion`, common denominator `∏_{a ∈ A, a < m} (2^a - 1)`)
applies, as in `Opn.erdos_257_long_gaps`. The proof is elementary and complete. -/
theorem Opn.erdos_257_lacunary_union :
    ∀ (r : ℕ) (c : Fin r → ℕ → ℕ), 0 < r → (∀ i, 0 < c i 0) →
    (∀ i j, (2 * r + 1) ^ (r + 1) * c i j ≤ c i (j + 1)) →
    Irrational (∑' n : (⋃ i, Set.range (c i) : Set ℕ), (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro r c hr h0 hR
  classical
  set R := (2 * r + 1) ^ (r + 1) with hRdef
  have hR2 : 2 ≤ R := by
    calc 2 ≤ 2 * r + 1 := by omega
      _ = (2 * r + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 * r + 1) ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  set A : Set ℕ := ⋃ i, Set.range (c i) with hA
  have hmemA : ∀ a, a ∈ A ↔ ∃ i, a ∈ Set.range (c i) := fun a => by
    rw [hA, Set.mem_iUnion]
  have hinf : A.Infinite :=
    Set.Infinite.mono (Set.subset_iUnion (fun i => Set.range (c i)) ⟨0, hr⟩)
      (Set.infinite_range_of_injective (lu_mono (c ⟨0, hr⟩) R hR2 (h0 _) (hR _)).injective)
  have h0A : 0 ∉ A := by
    intro h
    obtain ⟨i, j, hj⟩ := (hmemA 0).1 h
    have := lu_gt (c i) R hR2 (h0 i) (hR i) j
    omega
  apply r2_liou A hinf h0A
  intro C
  obtain ⟨k, _, hk⟩ := lu_window r c R hR2 le_rfl h0 hR C
  set T := (2 * r + 1) ^ k * C with hT
  have hCT : C ≤ T := by
    have := Nat.mul_le_mul_right C (Nat.one_le_pow k (2 * r + 1) (by omega))
    simpa [hT] using this
  obtain ⟨a0, ha0A, ha0⟩ := hinf.exists_gt T
  have hex : ∃ m, m ∈ A ∧ T < m := ⟨a0, ha0A, ha0⟩
  set m := Nat.find hex with hm
  obtain ⟨hmA, hTm⟩ := Nat.find_spec hex
  have hbelow : ∀ a ∈ A, a < m → a ≤ T := fun a ha ham => by
    by_contra h
    push_neg at h
    exact Nat.find_min hex ham ⟨ha, h⟩
  have hmbig : (2 * r + 1) * T < m := by
    obtain ⟨i, j, hij⟩ := (hmemA m).1 hmA
    have e : (2 * r + 1) ^ (k + 1) * C = (2 * r + 1) * T := by rw [hT]; ring
    rcases hk i j with h | h
    · rw [hij] at h; omega
    · rw [hij] at h; omega
  set F := (Finset.range m).filter (· ∈ A) with hF
  have hFmem : ∀ a, a ∈ F ↔ a < m ∧ a ∈ A := fun a => by
    rw [hF, Finset.mem_filter, Finset.mem_range]
  -- a chain index for each element
  let g : ℕ → Fin r := fun a =>
    if h : ∃ i, a ∈ Set.range (c i) then h.choose else ⟨0, hr⟩
  have hg : ∀ a ∈ A, a ∈ Set.range (c (g a)) := fun a ha => by
    have h := (hmemA a).1 ha
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hfib : ∀ i : Fin r, ∑ a ∈ F with g a = i, a ≤ 2 * T := fun i => by
    apply lu_geo_sum
    · intro a ha
      rw [Finset.mem_filter] at ha
      have := (hFmem a).1 ha.1
      exact hbelow a this.2 this.1
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      have haA := ((hFmem a).1 ha.1).2
      have hbA := ((hFmem b).1 hb.1).2
      obtain ⟨ja, hja⟩ := ha.2 ▸ hg a haA
      obtain ⟨jb, hjb⟩ := hb.2 ▸ hg b hbA
      have hmono := lu_mono (c i) R hR2 (h0 i) (hR i)
      have hj : ja < jb := by
        rw [← hja, ← hjb] at hab
        exact hmono.lt_iff_lt.1 hab
      have := lu_ratio (c i) R hR2 (h0 i) (hR i) _ _ hj
      have h2 : 2 * c i ja ≤ R * c i ja := Nat.mul_le_mul_right _ hR2
      omega
  have hsum : ∑ a ∈ F, a ≤ r * (2 * T) := by
    rw [← Finset.sum_fiberwise F g (fun a => a)]
    calc ∑ i : Fin r, ∑ a ∈ F with g a = i, a ≤ ∑ _i : Fin r, 2 * T :=
          Finset.sum_le_sum (fun i _ => hfib i)
      _ = r * (2 * T) := by simp
  refine ⟨m, hmA, ∏ a ∈ F, (2 ^ a - 1), ?_, ?_, ?_⟩
  · apply Finset.prod_pos
    intro a ha
    have haA := ((hFmem a).1 ha).2
    have hne : a ≠ 0 := fun h => h0A (h ▸ haA)
    have := Nat.one_lt_two_pow hne
    omega
  · intro a ha ham
    exact Finset.dvd_prod_of_mem _ ((hFmem a).2 ⟨ham, ha⟩)
  · have hL : ∏ a ∈ F, (2 ^ a - 1) ≤ 2 ^ (∑ a ∈ F, a) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun a _ => Nat.sub_le _ _)
    have e2 : (2 * r + 1) * T = r * (2 * T) + T := by ring
    calc 2 ^ C * ∏ a ∈ F, (2 ^ a - 1) ≤ 2 ^ C * 2 ^ (∑ a ∈ F, a) := Nat.mul_le_mul_left _ hL
      _ = 2 ^ (C + ∑ a ∈ F, a) := (pow_add _ _ _).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
