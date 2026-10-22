import Mathlib
import Nodes.«variant-f9c7b81b».Context

private noncomputable def tt (n : ℕ) : ℝ := 1 / (2 ^ n - 1)

private noncomputable def TT (N : ℕ) : ℝ := ∑' k, tt (k + N)

private lemma tt_eq (m : ℕ) : tt m = (1 / 2 : ℝ) ^ m / (1 - (1 / 2 : ℝ) ^ m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [tt]
  · have h2 : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
    have h3 : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    have hpos : (0 : ℝ) < (1 / 2) ^ m := by positivity
    have hlt : (1 / 2 : ℝ) ^ m < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hm.ne'
    unfold tt
    rw [div_eq_div_iff (by linarith) (by linarith)]
    nlinarith

private lemma half_pow_le (m : ℕ) (hm : 1 ≤ m) : (1 / 2 : ℝ) ^ m ≤ 1 / 2 := by
  calc (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ = 1 / 2 := by norm_num

private lemma tt_nonneg (m : ℕ) : 0 ≤ tt m := by
  rw [tt_eq]
  have hle : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact div_nonneg (by positivity) (by linarith)

private lemma tt_upper (m : ℕ) (hm : 1 ≤ m) :
    tt m ≤ (1 / 2 : ℝ) ^ m + 2 * ((1 / 2 : ℝ) ^ m) ^ 2 := by
  rw [tt_eq]
  have ha := half_pow_le m hm
  have hpos : (0 : ℝ) < (1 / 2) ^ m := by positivity
  set a := (1 / 2 : ℝ) ^ m
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg a, mul_pos hpos hpos]

private lemma tt_lower (m : ℕ) (hm : 1 ≤ m) :
    (1 / 2 : ℝ) ^ m + ((1 / 2 : ℝ) ^ m) ^ 2 < tt m := by
  rw [tt_eq]
  have ha := half_pow_le m hm
  have hpos : (0 : ℝ) < (1 / 2) ^ m := by positivity
  set a := (1 / 2 : ℝ) ^ m
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_pos (mul_pos hpos hpos) hpos]

private lemma tt_le_geom (m : ℕ) : tt m ≤ 2 * (1 / 2 : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [tt]
  · have h := tt_upper m hm
    have ha := half_pow_le m hm
    have hpos : (0 : ℝ) < (1 / 2) ^ m := by positivity
    nlinarith

private lemma tt_summable : Summable tt :=
  Summable.of_nonneg_of_le tt_nonneg tt_le_geom (summable_geometric_two.mul_left 2)

private lemma tt_summable_shift (N : ℕ) : Summable (fun k => tt (k + N)) :=
  (summable_nat_add_iff N).mpr tt_summable

private lemma TT_succ (N : ℕ) : TT N = tt N + TT (N + 1) := by
  unfold TT
  rw [(tt_summable_shift N).tsum_eq_zero_add]
  congr 1
  · simp
  · congr 1; funext k; congr 1; ring

private lemma TT_nonneg (N : ℕ) : 0 ≤ TT N := tsum_nonneg (fun k => tt_nonneg _)

private lemma geom_shift (N : ℕ) : ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + N) = 2 * (1 / 2) ^ N := by
  simp_rw [pow_add]
  rw [tsum_mul_right, tsum_geometric_two]

private lemma q4 (k : ℕ) : (1 / 4 : ℝ) ^ k = (1 / 2) ^ (2 * k) := by
  rw [pow_mul]; norm_num

private lemma geom4_shift (N : ℕ) :
    ∑' k : ℕ, ((1 / 2 : ℝ) ^ (k + N)) ^ 2 = 4 / 3 * ((1 / 2) ^ N) ^ 2 := by
  have : ∀ k : ℕ, ((1 / 2 : ℝ) ^ (k + N)) ^ 2 = (1 / 4) ^ k * ((1 / 2) ^ N) ^ 2 := by
    intro k
    rw [q4]
    ring
  simp_rw [this]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- `TT (M+1) ≤ (1/2)^M + (2/3)(1/4)^M`. -/
private lemma TT_upper (M : ℕ) :
    TT (M + 1) ≤ (1 / 2 : ℝ) ^ M + 2 / 3 * ((1 / 2 : ℝ) ^ M) ^ 2 := by
  unfold TT
  have hs1 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + (M + 1))) :=
    (summable_nat_add_iff (M + 1)).mpr summable_geometric_two
  have hs2 : Summable (fun k : ℕ => ((1 / 2 : ℝ) ^ (k + (M + 1))) ^ 2) := by
    have : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k * ((1 / 2) ^ (M + 1)) ^ 2) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
    refine this.congr (fun k => ?_)
    rw [q4]
    ring
  calc ∑' k, tt (k + (M + 1))
      ≤ ∑' k : ℕ, ((1 / 2 : ℝ) ^ (k + (M + 1)) + 2 * ((1 / 2 : ℝ) ^ (k + (M + 1))) ^ 2) :=
        Summable.tsum_le_tsum (fun k => tt_upper _ (by omega)) (tt_summable_shift _)
          (hs1.add (hs2.mul_left 2))
    _ = 2 * (1 / 2) ^ (M + 1) + 2 * (4 / 3 * ((1 / 2) ^ (M + 1)) ^ 2) := by
        rw [Summable.tsum_add hs1 (hs2.mul_left 2), tsum_mul_left, geom_shift, geom4_shift]
    _ = (1 / 2 : ℝ) ^ M + 2 / 3 * ((1 / 2 : ℝ) ^ M) ^ 2 := by ring

private lemma TT_lower (M : ℕ) : (1 / 2 : ℝ) ^ M ≤ TT (M + 1) := by
  unfold TT
  have hs1 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + (M + 1))) :=
    (summable_nat_add_iff (M + 1)).mpr summable_geometric_two
  calc (1 / 2 : ℝ) ^ M = ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + (M + 1)) := by
        rw [geom_shift]; ring
    _ ≤ ∑' k, tt (k + (M + 1)) :=
        Summable.tsum_le_tsum (fun k => by
          have := tt_lower (k + (M + 1)) (by omega)
          nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ (k + (M + 1)))]) hs1 (tt_summable_shift _)

/-- The gap lemma: `TT (N+1) < tt N` for `N ≥ 1`. -/
private lemma gap (N : ℕ) (hN : 1 ≤ N) : TT (N + 1) < tt N := by
  have h1 := TT_upper N
  have h2 := tt_lower N hN
  have hpos : (0 : ℝ) < (1 / 2) ^ N := by positivity
  nlinarith [mul_pos hpos hpos]

private noncomputable def gg (b : ℕ → Bool) : ℝ := ∑' n, if b n = true then tt n else 0

private lemma gg_term_le (b : ℕ → Bool) (n : ℕ) : (if b n = true then tt n else 0) ≤ tt n := by
  split_ifs
  · exact le_rfl
  · exact tt_nonneg n

private lemma gg_term_nonneg (b : ℕ → Bool) (n : ℕ) : 0 ≤ (if b n = true then tt n else 0) := by
  split_ifs
  · exact tt_nonneg n
  · exact le_rfl

private lemma gg_summable (b : ℕ → Bool) : Summable (fun n => if b n = true then tt n else 0) :=
  Summable.of_nonneg_of_le (gg_term_nonneg b) (gg_term_le b) tt_summable

private lemma gg_continuous : Continuous gg := by
  unfold gg
  refine continuous_tsum (u := tt) (fun n => ?_) tt_summable (fun n b => ?_)
  · exact (continuous_of_discreteTopology (f := fun c : Bool => if c = true then tt n else 0)).comp
      (continuous_apply n)
  · rw [Real.norm_eq_abs, abs_of_nonneg (gg_term_nonneg b n)]
    exact gg_term_le b n

private lemma CC_eq :
    {x : ℝ | ∃ A : Set ℕ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = x} = Set.range gg := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    classical
    refine ⟨fun n => decide (n ∈ A), ?_⟩
    unfold gg
    rw [show (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) = ∑' n : A, tt n.1 from rfl, tsum_subtype A tt]
    congr 1; funext n
    by_cases h : n ∈ A <;> simp [h, Set.indicator_apply]
  · rintro ⟨b, rfl⟩
    refine ⟨{n | b n = true}, ?_⟩
    unfold gg
    rw [show (∑' n : {n | b n = true}, (1 : ℝ) / (2 ^ n.1 - 1)) = ∑' n : {n | b n = true}, tt n.1
      from rfl, tsum_subtype {n | b n = true} tt]
    congr 1; funext n
    by_cases h : b n = true <;> simp [h, Set.indicator_apply]

private lemma CC_closed : IsClosed (Set.range gg) :=
  (isCompact_range gg_continuous).isClosed

private noncomputable def sF (F : Finset ℕ) : ℝ := ∑ n ∈ F, tt n

private lemma sF_mem (F : Finset ℕ) : sF F ∈ Set.range gg := by
  classical
  refine ⟨fun n => decide (n ∈ F), ?_⟩
  unfold gg sF
  rw [tsum_eq_sum (s := F)]
  · refine Finset.sum_congr rfl (fun n hn => by simp [hn])
  · intro n hn; simp [hn]

private noncomputable def CN (M : ℕ) : Set ℝ :=
  ⋃ F ∈ (Finset.Ico 1 (M + 1)).powerset, Set.Icc (sF F) (sF F + TT (M + 1))

private lemma gg_mem_CN (M : ℕ) (b : ℕ → Bool) : gg b ∈ CN M := by
  classical
  set f : ℕ → ℝ := fun n => if b n = true then tt n else 0 with hf
  have hsplit := (gg_summable b).sum_add_tsum_nat_add (M + 1)
  set F := (Finset.Ico 1 (M + 1)).filter (fun n => b n = true) with hF
  have hhead : ∑ i ∈ Finset.range (M + 1), f i = sF F := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    have h0 : f 0 = 0 := by simp [hf, tt]
    rw [h0, zero_add, sF, hF, Finset.sum_filter]
  have htail0 : 0 ≤ ∑' i, f (i + (M + 1)) := tsum_nonneg (fun i => gg_term_nonneg b _)
  have htail1 : ∑' i, f (i + (M + 1)) ≤ TT (M + 1) :=
    Summable.tsum_le_tsum (fun i => gg_term_le b _)
      ((summable_nat_add_iff (M + 1)).mpr (gg_summable b)) (tt_summable_shift _)
  simp only [CN, Set.mem_iUnion, Set.mem_Icc]
  refine ⟨F, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_, ?_⟩
  · have : gg b = ∑ i ∈ Finset.range (M + 1), f i + ∑' i, f (i + (M + 1)) := by
      rw [hsplit]; rfl
    rw [this, hhead]; linarith
  · have : gg b = ∑ i ∈ Finset.range (M + 1), f i + ∑' i, f (i + (M + 1)) := by
      rw [hsplit]; rfl
    rw [this, hhead]; linarith

private lemma pow_two_half (M : ℕ) : (2 : ℝ) ^ M * (1 / 2) ^ M = 1 := by
  rw [← mul_pow]; norm_num

private lemma vol_CN_le (M : ℕ) :
    MeasureTheory.volume (CN M) ≤ ENNReal.ofReal (2 ^ M * TT (M + 1)) := by
  unfold CN
  refine (MeasureTheory.measure_biUnion_finset_le _ _).trans (le_of_eq ?_)
  simp only [Real.volume_Icc, add_sub_cancel_left, Finset.sum_const, Finset.card_powerset,
    Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

private lemma upper (M : ℕ) : 2 ^ M * TT (M + 1) ≤ 1 + (1 / 2 : ℝ) ^ M := by
  have h := TT_upper M
  have h1 := pow_two_half M
  have hpos : (0 : ℝ) < (1 / 2) ^ M := by positivity
  have hle : (1 / 2 : ℝ) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) < 2 ^ M := by positivity
  calc (2 : ℝ) ^ M * TT (M + 1) ≤ 2 ^ M * ((1 / 2 : ℝ) ^ M + 2 / 3 * ((1 / 2 : ℝ) ^ M) ^ 2) :=
        mul_le_mul_of_nonneg_left h h2.le
    _ = 1 + 2 / 3 * (1 / 2 : ℝ) ^ M := by
        linear_combination (1 + 2 / 3 * (1 / 2 : ℝ) ^ M) * h1
    _ ≤ 1 + (1 / 2 : ℝ) ^ M := by linarith

private lemma vol_le_one : MeasureTheory.volume (Set.range gg) ≤ 1 := by
  have hb : ∀ M : ℕ, MeasureTheory.volume (Set.range gg) ≤ ENNReal.ofReal (1 + (1 / 2 : ℝ) ^ M) := by
    intro M
    calc MeasureTheory.volume (Set.range gg) ≤ MeasureTheory.volume (CN M) := by
          apply MeasureTheory.measure_mono
          rintro _ ⟨b, rfl⟩
          exact gg_mem_CN M b
      _ ≤ ENNReal.ofReal (2 ^ M * TT (M + 1)) := vol_CN_le M
      _ ≤ ENNReal.ofReal (1 + (1 / 2 : ℝ) ^ M) := ENNReal.ofReal_le_ofReal (upper M)
  have ht : Filter.Tendsto (fun M : ℕ => ENNReal.ofReal (1 + (1 / 2 : ℝ) ^ M)) Filter.atTop
      (nhds (ENNReal.ofReal (1 + 0))) := by
    apply ENNReal.tendsto_ofReal
    exact tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [add_zero, ENNReal.ofReal_one] at ht
  exact ge_of_tendsto' ht hb

private lemma TT_succ_le (N : ℕ) : TT (N + 1) ≤ TT N := by
  have := TT_succ N; have := tt_nonneg N; linarith

private lemma sub_Ico {M : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.Ico 1 (M + 2)) (hk : M + 1 ∉ F) :
    F ⊆ Finset.Ico 1 (M + 1) := by
  intro x hx
  have h1 := hF hx
  rw [Finset.mem_Ico] at h1 ⊢
  have : x ≠ M + 1 := fun h => hk (h ▸ hx)
  omega

private lemma erase_Ico {M : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.Ico 1 (M + 2)) :
    F.erase (M + 1) ⊆ Finset.Ico 1 (M + 1) := by
  intro x hx
  rw [Finset.mem_erase] at hx
  have h1 := hF hx.2
  rw [Finset.mem_Ico] at h1 ⊢
  omega

private lemma sF_erase {F : Finset ℕ} {k : ℕ} (hk : k ∈ F) : sF F = sF (F.erase k) + tt k := by
  unfold sF
  rw [Finset.sum_erase_add _ _ hk]

private lemma mixed (M : ℕ)
    (IH : ∀ F G : Finset ℕ, F ⊆ Finset.Ico 1 (M + 1) → G ⊆ Finset.Ico 1 (M + 1) → F ≠ G →
      TT (M + 1) < |sF F - sF G|)
    (F G : Finset ℕ) (hF : F ⊆ Finset.Ico 1 (M + 1)) (hG : G ⊆ Finset.Ico 1 (M + 1)) :
    TT (M + 2) < |sF F - (sF G + tt (M + 1))| := by
  have hgap := gap (M + 1) (by omega)
  have hsucc := TT_succ (M + 1)
  have ht := tt_nonneg (M + 1)
  have hT := TT_nonneg (M + 2)
  by_cases hFG : F = G
  · subst hFG
    rw [show sF F - (sF F + tt (M + 1)) = -tt (M + 1) by ring, abs_neg, abs_of_nonneg ht]
    exact hgap
  · have h := IH F G hF hG hFG
    rw [lt_abs] at h ⊢
    rcases h with h | h
    · left; linarith
    · right; linarith

private lemma sep (M : ℕ) : ∀ F G : Finset ℕ, F ⊆ Finset.Ico 1 (M + 1) → G ⊆ Finset.Ico 1 (M + 1) →
    F ≠ G → TT (M + 1) < |sF F - sF G| := by
  induction M with
  | zero =>
    intro F G hF hG hne
    exfalso; apply hne
    have h0 : Finset.Ico 1 (0 + 1) = ∅ := by simp
    rw [h0, Finset.subset_empty] at hF hG
    rw [hF, hG]
  | succ M IH =>
    intro F G hF hG hne
    have hle := TT_succ_le (M + 1)
    by_cases hkF : M + 1 ∈ F <;> by_cases hkG : M + 1 ∈ G
    · have hne' : F.erase (M + 1) ≠ G.erase (M + 1) := by
        intro h; apply hne
        rw [← Finset.insert_erase hkF, ← Finset.insert_erase hkG, h]
      have h := IH _ _ (erase_Ico hF) (erase_Ico hG) hne'
      rw [sF_erase hkF, sF_erase hkG, show sF (F.erase (M + 1)) + tt (M + 1) -
        (sF (G.erase (M + 1)) + tt (M + 1)) = sF (F.erase (M + 1)) - sF (G.erase (M + 1)) by ring]
      linarith
    · have h := mixed M IH G (F.erase (M + 1)) (sub_Ico hG hkG) (erase_Ico hF)
      rw [sF_erase hkF, abs_sub_comm]
      exact h
    · have h := mixed M IH F (G.erase (M + 1)) (sub_Ico hF hkF) (erase_Ico hG)
      rw [sF_erase hkG]
      exact h
    · have h := IH F G (sub_Ico hF hkF) (sub_Ico hG hkG) hne
      linarith

private lemma CN_meas (M : ℕ) : MeasurableSet (CN M) :=
  Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_Icc)

private lemma vol_CN_eq (M : ℕ) :
    MeasureTheory.volume (CN M) = ENNReal.ofReal (2 ^ M * TT (M + 1)) := by
  unfold CN
  rw [MeasureTheory.measure_biUnion_finset]
  · simp only [Real.volume_Icc, add_sub_cancel_left, Finset.sum_const, Finset.card_powerset,
      Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  · intro F hF G hG hne
    rw [Finset.mem_coe, Finset.mem_powerset] at hF hG
    have h := sep M F G hF hG hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Icc] at hx hx'
    rw [lt_abs] at h
    rcases h with h | h <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  · intro F _; exact measurableSet_Icc

private lemma vol_CN_ge (M : ℕ) : 1 ≤ MeasureTheory.volume (CN M) := by
  rw [vol_CN_eq, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have h := TT_lower M
  have h1 := pow_two_half M
  have h2 : (0 : ℝ) < 2 ^ M := by positivity
  nlinarith

private lemma CN_anti (M : ℕ) : CN (M + 1) ⊆ CN M := by
  intro x hx
  simp only [CN, Set.mem_iUnion, Set.mem_Icc, Finset.mem_powerset, exists_prop] at hx ⊢
  obtain ⟨F, hF, h1, h2⟩ := hx
  have hsucc := TT_succ (M + 1)
  have hle := TT_succ_le (M + 1)
  by_cases hk : M + 1 ∈ F
  · refine ⟨F.erase (M + 1), erase_Ico hF, ?_, ?_⟩
    · rw [sF_erase hk] at h1; linarith [tt_nonneg (M + 1)]
    · rw [sF_erase hk] at h2; linarith
  · exact ⟨F, sub_Ico hF hk, h1, by linarith⟩

private lemma iInter_sub : (⋂ M, CN M) ⊆ Set.range gg := by
  intro x hx
  rw [Set.mem_iInter] at hx
  rw [← CC_closed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (half_pos hε) (show (1 / 2 : ℝ) < 1 by norm_num)
  have hx' := hx M
  simp only [CN, Set.mem_iUnion, Set.mem_Icc, Finset.mem_powerset, exists_prop] at hx'
  obtain ⟨F, _, h1, h2⟩ := hx'
  refine ⟨sF F, sF_mem F, ?_⟩
  have hT := TT_upper M
  have hpos : (0 : ℝ) < (1 / 2) ^ M := by positivity
  have hle : (1 / 2 : ℝ) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

private lemma vol_ge_one : 1 ≤ MeasureTheory.volume (Set.range gg) := by
  calc (1 : ENNReal) ≤ ⨅ M, MeasureTheory.volume (CN M) := le_iInf vol_CN_ge
    _ = MeasureTheory.volume (⋂ M, CN M) := by
        rw [Antitone.measure_iInter (antitone_nat_of_succ_le CN_anti)
          (fun M => (CN_meas M).nullMeasurableSet)
          ⟨0, ne_top_of_le_ne_top ENNReal.ofReal_ne_top (vol_CN_le 0)⟩]
    _ ≤ MeasureTheory.volume (Set.range gg) := MeasureTheory.measure_mono iInter_sub

/-- The set of subset sums of the Mersenne reciprocals, `{Σ_{n∈A} 1/(2^n-1) : A ⊆ ℕ}`, has
Lebesgue measure exactly `1` (the term at `n = 0` is Lean's junk value `0`, so `A` and `A \ {0}`
give the same sum). It is a Cantor set (Kovač–Tao, arXiv:2406.17593, Rem. 4.1: distinct `A` give
distinct sums) of positive measure inside `[0, 1.6067…]`: about 62% of the interval. Erdős 257
asks whether it meets ℚ only in the sums of finite sets; its positive measure is why Kovač
(erdosproblems.com/257) expects the answer to be no. Proof: the sums of sets with prescribed
elements below `N` fill `2^(N-1)` disjoint intervals of length `T_N = Σ_{k≥N} 1/(2^k-1)`
(disjoint by the gap lemma), and `2^(N-1) T_N → 1`. -/
theorem Opn.erdos_257_subsum_set_volume :
    MeasureTheory.volume {x : ℝ | ∃ A : Set ℕ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = x} = 1 := by
  rw [CC_eq]
  exact le_antisymm vol_le_one vol_ge_one
