import Mathlib
import Nodes.«variant-c91009b9».Context

/- `w a n = 2^(n mod a) / (2^a - 1)`; this equals `∑_{j ≥ 1, a ∣ n + j} 2^(-j)`. -/
private noncomputable def w (a n : ℕ) : ℝ := (2:ℝ) ^ (n % a) / ((2:ℝ) ^ a - 1)

/- `D a n m = ∑_{j=1}^m [a ∣ n+j] 2^(m-j)`, defined recursively. -/
private def D (a n : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 * D a n m + if a ∣ n + m + 1 then 1 else 0

private lemma D_succ (a n m : ℕ) : D a n (m+1) = 2 * D a n m + if a ∣ n + m + 1 then 1 else 0 := rfl

private lemma two_pow_sub_one_nonneg (a : ℕ) : (0:ℝ) ≤ 2 ^ a - 1 := by
  have : (1:ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  linarith

private lemma two_pow_sub_one_pos {a : ℕ} (ha : 1 ≤ a) : (0:ℝ) < 2 ^ a - 1 := by
  have : (2:ℝ) ≤ 2 ^ a := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
  linarith

private lemma w_nonneg (a n : ℕ) : 0 ≤ w a n :=
  div_nonneg (by positivity) (two_pow_sub_one_nonneg a)

private lemma w_pos {a : ℕ} (ha : 1 ≤ a) (n : ℕ) : 0 < w a n :=
  div_pos (by positivity) (two_pow_sub_one_pos ha)

private lemma w_zero_left (n : ℕ) : w 0 n = 0 := by simp [w]

private lemma w_step (a n : ℕ) : 2 * w a n = w a (n+1) + if a ∣ n + 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [w_zero_left]
  have hpos := two_pow_sub_one_pos ha
  have hlt : n % a < a := Nat.mod_lt _ ha
  have hmod : (n + 1) % a = (n % a + 1) % a := by
    rw [Nat.add_mod, Nat.add_mod_mod]
  by_cases hc : n % a + 1 = a
  · have hd : a ∣ n + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, hmod, hc, Nat.mod_self]
    rw [if_pos hd]
    unfold w
    rw [Nat.dvd_iff_mod_eq_zero.mp hd]
    rw [show n % a = a - 1 by omega]
    field_simp
    have : (2:ℝ) ^ a = 2 * 2 ^ (a - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; simp
  · have h1 : (n + 1) % a = n % a + 1 := by rw [hmod]; exact Nat.mod_eq_of_lt (by omega)
    have hd : ¬ a ∣ n + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, h1]; omega
    rw [if_neg hd]
    unfold w
    rw [h1, pow_succ]
    ring

private lemma w_shift (a n m : ℕ) : 2 ^ m * w a n = w a (n+m) + D a n m := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    have h2 := w_step a (n + m)
    rw [pow_succ, mul_comm _ (2:ℝ), mul_assoc, ih, mul_add, h2, D_succ]
    have : n + m + 1 = n + (m + 1) := by ring
    rw [this]
    split_ifs <;> push_cast <;> ring

private lemma D_eq_zero_of_lt {a n m : ℕ} (h : n + m < a) : D a n m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [D_succ, ih (by omega)]
    have : ¬ a ∣ n + m + 1 := fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega
    simp [this]

private lemma D_of_dvd {a n m : ℕ} (h : a ∣ n) : D a n m = D a 0 m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [D_succ, D_succ, ih]
    have : a ∣ n + m + 1 ↔ a ∣ 0 + m + 1 := by
      rw [zero_add, add_assoc]
      exact (Nat.dvd_add_right h)
    simp only [this]

private lemma D_forced {b n m : ℕ} (hm1 : 1 ≤ m) (hm : m < b) (hb : b ∣ n + m) : D b n m = 1 := by
  have aux : ∀ k, k < m → D b n k = 0 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [D_succ, ih (by omega)]
      have : ¬ b ∣ n + k + 1 := fun hd => by
        have h3 : b ∣ (n + m) - (n + k + 1) := Nat.dvd_sub hb hd
        have h4 : (n + m) - (n + k + 1) = m - (k + 1) := by omega
        rw [h4] at h3
        have := Nat.le_of_dvd (by omega) h3
        omega
      simp [this]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [D_succ, aux k (by omega)]
  have : b ∣ n + k + 1 := by simpa [add_assoc] using hb
  simp [this]

private lemma w_le_one (a n : ℕ) : w a n ≤ 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [w_zero_left]
  have hpos := two_pow_sub_one_pos ha
  unfold w
  rw [div_le_one hpos]
  have hlt : n % a ≤ a - 1 := by have := Nat.mod_lt n ha; omega
  have h1 : (2:ℝ) ^ (n % a) ≤ 2 ^ (a - 1) := pow_le_pow_right₀ (by norm_num) hlt
  have h2 : (2:ℝ) ^ a = 2 * 2 ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h3 : (1:ℝ) ≤ 2 ^ (a - 1) := one_le_pow₀ (by norm_num)
  linarith

private lemma w_le_of_mod_le {a n m : ℕ} (h : n % a ≤ m) : w a n ≤ 2 ^ m / (2 ^ a - 1) := by
  unfold w
  gcongr
  · exact two_pow_sub_one_nonneg a
  · norm_num

private lemma one_div_two_pow_sub_one_le (a : ℕ) : 1 / ((2:ℝ) ^ a - 1) ≤ 2 * (1/2) ^ a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hpos := two_pow_sub_one_pos ha
  have h2 : (2:ℝ) ≤ 2 ^ a := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
  rw [div_le_iff₀ hpos]
  have : (1/2:ℝ) ^ a * 2 ^ a = 1 := by rw [← mul_pow]; norm_num
  have h0 : (0:ℝ) ≤ (1/2) ^ a := by positivity
  nlinarith

private lemma w_le_geom (a n : ℕ) : w a n ≤ 2 ^ (n+1) * (1/2) ^ a := by
  have h1 : w a n ≤ 2 ^ n / (2 ^ a - 1) := w_le_of_mod_le (Nat.mod_le n a)
  have h2 := one_div_two_pow_sub_one_le a
  calc w a n ≤ 2 ^ n / (2 ^ a - 1) := h1
    _ = 2 ^ n * (1 / (2 ^ a - 1)) := by ring
    _ ≤ 2 ^ n * (2 * (1/2) ^ a) := by gcongr
    _ = 2 ^ (n+1) * (1/2) ^ a := by ring

private lemma summable_w (U : Set ℕ) (n : ℕ) : Summable (U.indicator (fun a => w a n)) := by
  refine Summable.of_nonneg_of_le (f := fun a => 2 ^ (n+1) * (1/2:ℝ) ^ a) ?_ ?_ ?_
  · intro a; exact Set.indicator_nonneg (fun a _ => w_nonneg a n) a
  · intro a
    by_cases ha : a ∈ U
    · rw [Set.indicator_of_mem ha]; exact w_le_geom a n
    · rw [Set.indicator_of_notMem ha]; positivity
  · exact summable_geometric_two.mul_left _

private lemma block_sum {a L : ℕ} (ha : 1 ≤ a) (hc : Nat.Coprime a L) (M : ℕ) :
    ∑ s ∈ Finset.range a, w a (M + s * L) = 1 := by
  have hpos := two_pow_sub_one_pos ha
  have hinj : Set.InjOn (fun s => (M + s * L) % a) (Finset.range a) := by
    intro s hs s' hs' h
    simp only [Finset.coe_range, Set.mem_Iio] at hs hs'
    have h1 : M + s * L ≡ M + s' * L [MOD a] := h
    have h2 : s * L ≡ s' * L [MOD a] := Nat.ModEq.add_left_cancel' M h1
    have h3 : s ≡ s' [MOD a] := Nat.ModEq.cancel_right_of_coprime hc h2
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs'] at h3
  have himg : (Finset.range a).image (fun s => (M + s * L) % a) = Finset.range a := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      simp only [Finset.mem_image, Finset.mem_range] at hr ⊢
      obtain ⟨s, _, rfl⟩ := hr
      exact Nat.mod_lt _ (by omega)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ s ∈ Finset.range a, w a (M + s * L)
      = ∑ r ∈ (Finset.range a).image (fun s => (M + s * L) % a), (2:ℝ) ^ r / (2 ^ a - 1) := by
        rw [Finset.sum_image hinj]; rfl
    _ = ∑ r ∈ Finset.range a, (2:ℝ) ^ r / (2 ^ a - 1) := by rw [himg]
    _ = 1 := by
        rw [← Finset.sum_div, geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
        norm_num
        exact hpos.ne'

private lemma ap_block {a L : ℕ} (ha : 1 ≤ a) (hc : Nat.Coprime a L) (N0 : ℕ) (k : ℕ) :
    ∑ t ∈ Finset.range (a * k), w a (N0 + t * L) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have h := block_sum ha hc (N0 + a * k * L)
    have : ∑ x ∈ Finset.range a, w a (N0 + (a * k + x) * L) = 1 := by
      rw [← h]; apply Finset.sum_congr rfl; intro x _; congr 1; ring
    rw [this]; push_cast; ring

private lemma ap_sum_le {a L : ℕ} (ha : 1 ≤ a) (hc : Nat.Coprime a L) (N0 X : ℕ) :
    ∑ t ∈ Finset.range X, w a (N0 + t * L) ≤ (X:ℝ) / a + 1 := by
  have hX : X ≤ a * (X / a + 1) := (Nat.lt_mul_div_succ X (by omega)).le
  calc ∑ t ∈ Finset.range X, w a (N0 + t * L) ≤ ∑ t ∈ Finset.range (a * (X / a + 1)), w a (N0 + t * L) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hX) (fun _ _ _ => w_nonneg _ _)
    _ = ((X / a + 1 : ℕ) : ℝ) := ap_block ha hc N0 _
    _ ≤ (X:ℝ) / a + 1 := by
        push_cast
        linarith [Nat.cast_div_le (α := ℝ) (m := X) (n := a)]

private lemma pow_aux (Y d : ℕ) : ((2:ℝ) ^ Y - 1) * (Y + d) ≤ Y * (2 ^ (Y + d) - 1) := by
  induction d with
  | zero => simp; ring_nf; rfl
  | succ d ih =>
    push_cast
    have h1 : (2:ℝ) ^ (Y + (d + 1)) = 2 * 2 ^ (Y + d) := by ring
    rw [h1]
    have h2 : (2:ℝ) ^ Y ≤ 2 ^ (Y + d) := pow_le_pow_right₀ (by norm_num) (by omega)
    rcases Nat.eq_zero_or_pos Y with rfl | hY
    · simp
    · have hY' : (1:ℝ) ≤ Y := by exact_mod_cast hY
      have h3 : (0:ℝ) ≤ 2 ^ (Y + d) := by positivity
      nlinarith

private lemma range_sum_le {a : ℕ} (ha : 1 ≤ a) (Y : ℕ) :
    ∑ n ∈ Finset.range Y, w a n ≤ 2 * (Y:ℝ) / a := by
  have hapos : (0:ℝ) < a := by exact_mod_cast ha
  rcases le_or_gt a Y with h | h
  · have := ap_sum_le ha (Nat.coprime_one_right a) 0 Y
    simp only [zero_add, mul_one] at this
    have h1 : (1:ℝ) ≤ Y / a := by
      rw [le_div_iff₀ hapos]; exact_mod_cast (by omega : 1 * a ≤ Y)
    calc _ ≤ (Y:ℝ) / a + 1 := this
      _ ≤ 2 * Y / a := by rw [mul_div_assoc]; linarith
  · have hmod : ∀ n ∈ Finset.range Y, w a n = 2 ^ n / (2 ^ a - 1) := by
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [w, Nat.mod_eq_of_lt (by omega : n < a)]
    rw [Finset.sum_congr rfl hmod, ← Finset.sum_div, geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
    obtain ⟨d, rfl⟩ : ∃ d, a = Y + d := ⟨a - Y, by omega⟩
    have := pow_aux Y d
    have hpos := two_pow_sub_one_pos ha
    norm_num
    push_cast at hapos
    rw [div_le_div_iff₀ hpos hapos]
    have hY : (0:ℝ) ≤ Y := by positivity
    nlinarith

private lemma ap_sum_le' {a L : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (N0 X : ℕ) :
    ∑ t ∈ Finset.range X, w a (N0 + t * L) ≤ 2 * ((N0:ℝ) + X * L) / a := by
  have hinj : Set.InjOn (fun t => N0 + t * L) (Finset.range X) := by
    intro s _ s' _ h
    have := Nat.add_left_cancel h
    exact Nat.eq_of_mul_eq_mul_right hL this
  calc ∑ t ∈ Finset.range X, w a (N0 + t * L)
      = ∑ n ∈ (Finset.range X).image (fun t => N0 + t * L), w a n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.range (N0 + X * L), w a n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => w_nonneg _ _)
        intro n hn
        simp only [Finset.mem_image, Finset.mem_range] at hn ⊢
        obtain ⟨t, ht, rfl⟩ := hn
        nlinarith
    _ ≤ 2 * ((N0 + X * L : ℕ) : ℝ) / a := range_sum_le ha _
    _ = _ := by push_cast; ring

private lemma summable_inv_sub {A U : Set ℕ} (hUA : U ⊆ A)
    (hA : Summable (A.indicator fun a : ℕ => (1:ℝ) / a)) :
    Summable (U.indicator fun a : ℕ => (1:ℝ) / a) := by
  refine Summable.of_nonneg_of_le (fun b => ?_) (fun b => ?_) hA
  · exact Set.indicator_nonneg (fun a _ => by positivity) b
  · exact Set.indicator_le_indicator_of_subset hUA (fun a => by positivity) b

private lemma tail_small (A : Set ℕ) (hA : Summable (A.indicator fun a : ℕ => (1:ℝ) / a))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K, ∀ U ⊆ A, (∀ a ∈ U, K ≤ a) → ∑' a, U.indicator (fun a : ℕ => (1:ℝ) / a) a ≤ ε := by
  have ht := tendsto_sum_nat_add (A.indicator fun a : ℕ => (1:ℝ) / a)
  obtain ⟨K, hK⟩ := (ht.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨K, fun U hUA hUK => ?_⟩
  have hU := summable_inv_sub hUA hA
  rw [← hU.sum_add_tsum_nat_add K]
  have h0 : ∑ i ∈ Finset.range K, U.indicator (fun a : ℕ => (1:ℝ) / a) i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    exact Set.indicator_of_notMem (fun h => by have := hUK i h; omega) _
  rw [h0, zero_add]
  refine le_trans ?_ (hK K le_rfl).le
  refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff K).mpr hU)
    ((summable_nat_add_iff K).mpr hA)
  exact Set.indicator_le_indicator_of_subset hUA (fun a => by positivity) _

private lemma exists_good (A U : Set ℕ) (hUA : U ⊆ A)
    (hA : Summable (A.indicator fun a : ℕ => (1:ℝ) / a))
    (L N0 Z X : ℕ) (hL : 1 ≤ L) (hU1 : ∀ a ∈ U, 1 ≤ a) (hcop : ∀ a ∈ U, Nat.Coprime a L)
    (ε1 ε2 δ : ℝ)
    (h1 : ∑' a, U.indicator (fun a : ℕ => (1:ℝ) / a) a ≤ ε1)
    (h2 : ∑' a, (U ∩ Set.Ioi Z).indicator (fun a : ℕ => (1:ℝ) / a) a ≤ ε2)
    (hX : (X:ℝ) * ε1 + (Z + 1) + 2 * (N0 + X * L) * ε2 < X * δ) :
    ∃ t < X, ∑' a, U.indicator (fun a => w a (N0 + t * L)) a < δ := by
  by_contra hcon
  push_neg at hcon
  set Y : ℝ := (N0:ℝ) + X * L with hY
  have hYnn : 0 ≤ Y := by positivity
  have hsU := summable_inv_sub hUA hA
  have hsU2 := summable_inv_sub (Set.inter_subset_left.trans hUA : U ∩ Set.Ioi Z ⊆ A) hA
  have hzero : ∀ b ∉ Finset.range (Z+1), (U ∩ Set.Iic Z).indicator (fun _ : ℕ => (1:ℝ)) b = 0 := by
    intro b hb
    apply Set.indicator_of_notMem
    simp only [Finset.mem_range] at hb
    intro h
    have := h.2
    simp only [Set.mem_Iic] at this
    omega
  have hfin : Summable ((U ∩ Set.Iic Z).indicator (fun _ : ℕ => (1:ℝ))) :=
    summable_of_ne_finset_zero hzero
  have hfin_le : ∑' a, (U ∩ Set.Iic Z).indicator (fun _ : ℕ => (1:ℝ)) a ≤ Z + 1 := by
    rw [tsum_eq_sum hzero]
    calc ∑ b ∈ Finset.range (Z+1), (U ∩ Set.Iic Z).indicator (fun _ : ℕ => (1:ℝ)) b
        ≤ ∑ b ∈ Finset.range (Z+1), (1:ℝ) := by
          apply Finset.sum_le_sum
          intro b _
          by_cases hb : b ∈ U ∩ Set.Iic Z
          · rw [Set.indicator_of_mem hb]
          · rw [Set.indicator_of_notMem hb]; norm_num
      _ = Z + 1 := by simp
  have hbound : ∀ a, ∑ t ∈ Finset.range X, U.indicator (fun a => w a (N0 + t * L)) a ≤
      (X:ℝ) * U.indicator (fun a : ℕ => (1:ℝ) / a) a
        + (U ∩ Set.Iic Z).indicator (fun _ => (1:ℝ)) a
        + 2 * Y * (U ∩ Set.Ioi Z).indicator (fun a : ℕ => (1:ℝ) / a) a := by
    intro a
    by_cases ha : a ∈ U
    · simp only [Set.indicator_of_mem ha]
      by_cases hz : a ≤ Z
      · rw [Set.indicator_of_mem (show a ∈ U ∩ Set.Iic Z from ⟨ha, hz⟩),
          Set.indicator_of_notMem (show a ∉ U ∩ Set.Ioi Z from fun h => by
            have := h.2; simp only [Set.mem_Ioi] at this; omega)]
        have := ap_sum_le (hU1 a ha) (hcop a ha) N0 X
        calc _ ≤ (X:ℝ) / a + 1 := this
          _ = _ := by ring
      · rw [Set.indicator_of_notMem (show a ∉ U ∩ Set.Iic Z from fun h => by
            have := h.2; simp only [Set.mem_Iic] at this; omega),
          Set.indicator_of_mem (show a ∈ U ∩ Set.Ioi Z from ⟨ha, by simp only [Set.mem_Ioi]; omega⟩)]
        have := ap_sum_le' (hU1 a ha) hL N0 X
        have h0 : (0:ℝ) ≤ X * (1 / a) := by positivity
        calc _ ≤ 2 * Y / a := this
          _ ≤ _ := by rw [div_eq_mul_one_div (2 * Y)]; linarith
    · simp [Set.indicator_of_notMem ha, Set.indicator_of_notMem (fun h : a ∈ U ∩ _ => ha h.1)]
  have hsumX : (X:ℝ) * δ ≤ ∑ t ∈ Finset.range X, ∑' a, U.indicator (fun a => w a (N0 + t * L)) a := by
    calc (X:ℝ) * δ = ∑ t ∈ Finset.range X, δ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t ht => hcon t (Finset.mem_range.mp ht))
  rw [← Summable.tsum_finsetSum (fun t _ => summable_w U _)] at hsumX
  have hle := Summable.tsum_le_tsum hbound (summable_sum (fun t _ => summable_w U _))
    (((hsU.mul_left (X:ℝ)).add hfin).add (hsU2.mul_left (2 * Y)))
  rw [Summable.tsum_add ((hsU.mul_left (X:ℝ)).add hfin) (hsU2.mul_left (2 * Y)),
    Summable.tsum_add (hsU.mul_left (X:ℝ)) hfin, tsum_mul_left, tsum_mul_left] at hle
  have hX0 : (0:ℝ) ≤ X := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hX0,
    mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * Y)]

/- `R A q n = q * ∑_{a ∈ A} 2^(n mod a)/(2^a - 1)`. -/
private noncomputable def R (A : Set ℕ) (q n : ℕ) : ℝ := q * ∑' a, A.indicator (fun a => w a n) a

private lemma R_shift (A : Set ℕ) (q N m : ℕ) :
    2 ^ m * R A q N = R A q (N + m) + q * ∑' a, A.indicator (fun a => (D a N m : ℝ)) a := by
  have key : A.indicator (fun a => (D a N m : ℝ)) = fun a =>
      2 ^ m * A.indicator (fun a => w a N) a - A.indicator (fun a => w a (N + m)) a := by
    funext a
    by_cases ha : a ∈ A
    · simp only [Set.indicator_of_mem ha]; rw [w_shift]; ring
    · simp [Set.indicator_of_notMem ha]
  rw [key, Summable.tsum_sub ((summable_w A N).mul_left _) (summable_w A (N + m)), tsum_mul_left]
  unfold R; ring

private lemma tsum_D_nat (A : Set ℕ) (N m : ℕ) :
    ∃ k : ℕ, ∑' a, A.indicator (fun a => (D a N m : ℝ)) a = k := by
  refine ⟨∑ a ∈ Finset.range (N + m + 1), A.indicator (fun a => D a N m) a, ?_⟩
  rw [tsum_eq_sum (s := Finset.range (N + m + 1))]
  · push_cast
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ A <;> simp [ha]
  · intro a ha
    simp only [Finset.mem_range] at ha
    by_cases h : a ∈ A
    · simp [Set.indicator_of_mem h, D_eq_zero_of_lt (by omega : N + m < a)]
    · simp [h]

private lemma R_int (A : Set ℕ) (q : ℕ) (p : ℤ) (h0 : R A q 0 = p) (n : ℕ) : ∃ z : ℤ, R A q n = z := by
  obtain ⟨k, hk⟩ := tsum_D_nat A 0 n
  have := R_shift A q 0 n
  rw [h0, hk, zero_add] at this
  exact ⟨2 ^ n * p - q * k, by push_cast; linarith⟩

private lemma R_pos (A : Set ℕ) (q : ℕ) (hq : 0 < q) {a : ℕ} (ha : a ∈ A) (ha1 : 1 ≤ a) (n : ℕ) :
    0 < R A q n := by
  unfold R
  apply mul_pos (by exact_mod_cast hq)
  apply (summable_w A n).tsum_pos (fun i => Set.indicator_nonneg (fun _ _ => w_nonneg _ _) i) a
  rw [Set.indicator_of_mem ha]; exact w_pos ha1 n

private lemma sum_beta (F : Finset ℕ) (m : ℕ) :
    ∑ a ∈ F, min 1 ((2:ℝ) ^ m / (2 ^ a - 1)) ≤ m + 3 := by
  set g : ℕ → ℝ := fun a => if a ≤ m then 1 else 2 ^ (m + 1) * (1/2) ^ a with hg
  have hgnn : ∀ a, 0 ≤ g a := by intro a; simp only [hg]; split_ifs <;> positivity
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le hgnn (fun a => ?_) (summable_geometric_two.mul_left (2 ^ (m+1)))
    simp only [hg]
    split_ifs with h
    · have h1 : (2:ℝ) ^ a ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2:ℝ) ^ a * (1/2) ^ a = 1 := by rw [← mul_pow]; norm_num
      have h3 : (0:ℝ) ≤ (1/2) ^ a := by positivity
      nlinarith
    · exact le_rfl
  have hle : ∀ a, min 1 ((2:ℝ) ^ m / (2 ^ a - 1)) ≤ g a := by
    intro a
    simp only [hg]
    split_ifs with h
    · exact min_le_left _ _
    · refine (min_le_right _ _).trans ?_
      have := one_div_two_pow_sub_one_le a
      calc (2:ℝ) ^ m / (2 ^ a - 1) = 2 ^ m * (1 / (2 ^ a - 1)) := by ring
        _ ≤ 2 ^ m * (2 * (1/2) ^ a) := by gcongr
        _ = _ := by ring
  have htsum : ∑' a, g a = m + 3 := by
    rw [← hgs.sum_add_tsum_nat_add (m + 1)]
    have e1 : ∑ i ∈ Finset.range (m + 1), g i = m + 1 := by
      rw [Finset.sum_congr rfl (fun i hi => by simp only [hg]; rw [if_pos (by simp at hi; omega)])]
      simp
    have e2 : ∀ i, g (i + (m + 1)) = (1/2) ^ i := by
      intro i
      show (if i + (m + 1) ≤ m then (1:ℝ) else 2 ^ (m + 1) * (1/2) ^ (i + (m + 1))) = _
      rw [if_neg (by omega), pow_add (1/2:ℝ) i (m + 1)]
      have : (2:ℝ) ^ (m + 1) * (1/2) ^ (m + 1) = 1 := by rw [← mul_pow]; norm_num
      calc (2:ℝ) ^ (m + 1) * ((1/2) ^ i * (1/2) ^ (m + 1))
          = (2 ^ (m + 1) * (1/2) ^ (m + 1)) * (1/2) ^ i := by ring
        _ = _ := by rw [this, one_mul]
    rw [e1, tsum_congr e2, tsum_geometric_two]
    ring
  calc ∑ a ∈ F, min 1 ((2:ℝ) ^ m / (2 ^ a - 1)) ≤ ∑ a ∈ F, g a := Finset.sum_le_sum (fun a _ => hle a)
    _ ≤ ∑' a, g a := hgs.sum_le_tsum F (fun i _ => hgnn i)
    _ = m + 3 := htsum

private lemma exists_m (q : ℕ) : ∃ m : ℕ, 1 ≤ m ∧ (q:ℝ) * (m + 4) < 2 ^ m := by
  refine ⟨2 * (2 * q + 3), by omega, ?_⟩
  have hk : 2 * q + 3 < 2 ^ (2 * q + 3) := Nat.lt_two_pow_self
  have : q * (2 * (2 * q + 3) + 4) < 2 ^ (2 * (2 * q + 3)) := by
    rw [pow_mul']
    nlinarith
  exact_mod_cast this

private lemma main_contra (A : Set ℕ) (hinf : A.Infinite) (hcop : A.Pairwise Nat.Coprime)
    (hpos : ∀ a ∈ A, 1 ≤ a) (hA : Summable (A.indicator fun a : ℕ => (1:ℝ) / a))
    (q : ℕ) (hq : 0 < q) (p : ℤ) (h0 : R A q 0 = p) : False := by
  classical
  obtain ⟨m, hm1, hmq⟩ := exists_m q
  set δ : ℝ := 1 / 2 ^ m with hδ
  have hδpos : 0 < δ := by positivity
  have hδm : (2:ℝ) ^ m * δ = 1 := by rw [hδ]; field_simp
  obtain ⟨K1, hK1⟩ := tail_small A hA (δ / 4) (by positivity)
  set K := K1 + m with hK
  set C0 : Finset ℕ := (Finset.range (K + 1)).filter (· ∈ A) with hC0
  set c := ∑ a ∈ C0, D a 0 m with hc
  set r := 2 ^ m - c % 2 ^ m with hr
  have hAK : (A \ Set.Iic K).Infinite := hinf.diff (Set.finite_Iic K)
  obtain ⟨B, hBsub, hBcard⟩ := hAK.exists_subset_card_eq r
  have hBA : ∀ b ∈ B, b ∈ A := fun b hb => (hBsub hb).1
  have hBK : ∀ b ∈ B, K < b := fun b hb => by
    have := (hBsub hb).2; simp only [Set.mem_Iic, not_le] at this; exact this
  have hC0A : ∀ a ∈ C0, a ∈ A := fun a ha => (Finset.mem_filter.mp ha).2
  have hC0K : ∀ a ∈ C0, a ≤ K := fun a ha => by
    have := (Finset.mem_filter.mp ha).1; simp only [Finset.mem_range] at this; omega
  have hdisj : Disjoint C0 B := by
    rw [Finset.disjoint_left]; intro a ha hb; have := hC0K a ha; have := hBK a hb; omega
  set F := C0 ∪ B with hF
  have hFA : ∀ a ∈ F, a ∈ A := by
    intro a ha; rcases Finset.mem_union.mp ha with h | h; exact hC0A a h; exact hBA a h
  set P := ∏ a ∈ C0, a with hP
  set Q := ∏ b ∈ B, b with hQ
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a ha => by
    have := hpos a (hC0A a ha); omega)
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a ha => by
    have := hpos a (hBA a ha); omega)
  have hPQ : Nat.Coprime P Q := by
    apply Nat.Coprime.prod_left; intro a ha; apply Nat.Coprime.prod_right; intro b hb
    exact hcop (hC0A a ha) (hBA b hb) (fun h => by subst h; exact Finset.disjoint_left.mp hdisj ha hb)
  set N0 : ℕ := (Nat.chineseRemainder hPQ 0 (Q - m % Q) : ℕ) with hN0
  have hN0P : N0 ≡ 0 [MOD P] := (Nat.chineseRemainder hPQ 0 (Q - m % Q)).2.1
  have hN0Q : N0 ≡ Q - m % Q [MOD Q] := (Nat.chineseRemainder hPQ 0 (Q - m % Q)).2.2
  have hN0lt : N0 < P * Q := Nat.chineseRemainder_lt_mul hPQ _ _ hP0 hQ0
  set L := P * Q with hL
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero (mul_ne_zero hP0 hQ0)
  have hPN0 : P ∣ N0 := Nat.modEq_zero_iff_dvd.mp hN0P
  have hQN0 : Q ∣ N0 + m := by
    have h1 : (N0 + m) % Q = (Q - m % Q + m) % Q := Nat.ModEq.add_right m hN0Q
    have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
    have h2 := Nat.mod_lt m hQpos
    have h3 := Nat.mod_add_div m Q
    have h4 : Q - m % Q + m = Q * (m / Q + 1) := by rw [mul_add, mul_one]; omega
    rw [Nat.dvd_iff_mod_eq_zero, h1, h4, Nat.mul_mod_right]
  -- the uncontrolled elements
  set U : Set ℕ := A \ (↑F : Set ℕ) with hU
  have hUA : U ⊆ A := Set.diff_subset
  have hU1 : ∀ a ∈ U, 1 ≤ a := fun a ha => hpos a ha.1
  have hUK : ∀ a ∈ U, K < a := by
    intro a ha
    by_contra hcon
    apply ha.2
    exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ha.1⟩))
  have hcopU : ∀ a ∈ U, Nat.Coprime a L := by
    intro a ha
    have hne : ∀ x ∈ F, a ≠ x := fun x hx h => ha.2 (by rw [h]; exact_mod_cast hx)
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.prod_right; intro x hx
      exact hcop ha.1 (hC0A x hx) (hne x (Finset.mem_union_left _ hx))
    · apply Nat.Coprime.prod_right; intro x hx
      exact hcop ha.1 (hBA x hx) (hne x (Finset.mem_union_right _ hx))
  have h1 : ∑' a, U.indicator (fun a : ℕ => (1:ℝ) / a) a ≤ δ / 4 :=
    hK1 U hUA (fun a ha => by have := hUK a ha; omega)
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL1
  obtain ⟨Z, hZ⟩ := tail_small A hA (δ / (16 * L)) (by positivity)
  have h2 : ∑' a, (U ∩ Set.Ioi Z).indicator (fun a : ℕ => (1:ℝ) / a) a ≤ δ / (16 * L) :=
    hZ _ (Set.inter_subset_left.trans hUA) (fun a ha => le_of_lt ha.2)
  set X : ℕ := 4 * (Z + 1) * 2 ^ m + 1 with hX
  have hXδ : (X:ℝ) * δ = 4 * (Z + 1) + δ := by
    rw [hX]; push_cast
    have : (4 * ((Z:ℝ) + 1) * 2 ^ m + 1) * δ = 4 * (Z + 1) * (2 ^ m * δ) + δ := by ring
    rw [this, hδm]; ring
  have hX1 : (1:ℝ) ≤ X := by
    rw [hX]; push_cast
    have : (0:ℝ) ≤ 4 * (Z+1) * 2^m := by positivity
    linarith
  have hN0L : (N0:ℝ) < L := by exact_mod_cast hN0lt
  have hbig : 2 * ((N0:ℝ) + X * L) * (δ / (16 * L)) ≤ (1 + X) * δ / 8 := by
    calc 2 * ((N0:ℝ) + X * L) * (δ / (16 * L)) = ((N0:ℝ) + X * L) * δ / (8 * L) := by
          field_simp; ring
      _ ≤ (L * (1 + X)) * δ / (8 * L) := by gcongr; nlinarith
      _ = (1 + X) * δ / 8 := by field_simp
  have hXcond : (X:ℝ) * (δ / 4) + (Z + 1) + 2 * (N0 + X * L) * (δ / (16 * L)) < X * δ := by
    nlinarith
  obtain ⟨t, -, hV⟩ := exists_good A U hUA hA L N0 Z X hL1 hU1 hcopU (δ / 4) (δ / (16 * L)) δ
    h1 h2 hXcond
  set N := N0 + t * L with hNdef
  set V := ∑' a, U.indicator (fun a => w a N) a with hVdef
  -- divisibility facts
  have hC0N : ∀ a ∈ C0, a ∣ N := by
    intro a ha
    have haP : a ∣ P := Finset.dvd_prod_of_mem (fun x => x) ha
    exact Nat.dvd_add (haP.trans hPN0) (Dvd.dvd.mul_left (haP.trans (Dvd.intro Q rfl)) t)
  have hBN : ∀ b ∈ B, b ∣ N + m := by
    intro b hb
    have hbQ : b ∣ Q := Finset.dvd_prod_of_mem (fun x => x) hb
    have : N + m = (N0 + m) + t * L := by rw [hNdef]; ring
    rw [this]
    exact Nat.dvd_add (hbQ.trans hQN0) (Dvd.dvd.mul_left (hbQ.trans (Dvd.intro_left P rfl)) t)
  have hwU : ∀ a ∈ U, 2 ^ m * w a N < 1 := by
    intro a ha
    have hle : w a N ≤ V := by
      have := (summable_w U N).le_tsum a (fun j _ => Set.indicator_nonneg (fun _ _ => w_nonneg _ _) j)
      rwa [Set.indicator_of_mem ha] at this
    calc 2 ^ m * w a N ≤ 2 ^ m * V := by gcongr
      _ < 2 ^ m * δ := by gcongr
      _ = 1 := hδm
  have hDU : ∀ a ∈ U, D a N m = 0 := by
    intro a ha
    have h := w_shift a N m
    have h' := hwU a ha
    have hw := w_nonneg a (N + m)
    have : (D a N m : ℝ) < 1 := by linarith
    exact_mod_cast (show D a N m < 1 by exact_mod_cast this) |> Nat.lt_one_iff.mp
  -- the D-sum
  have hsumD : ∑' a, A.indicator (fun a => (D a N m : ℝ)) a = ((c + r : ℕ) : ℝ) := by
    rw [tsum_eq_sum (s := F)]
    · have e1 : ∑ a ∈ F, A.indicator (fun a => (D a N m : ℝ)) a = ∑ a ∈ F, (D a N m : ℝ) :=
        Finset.sum_congr rfl (fun a ha => Set.indicator_of_mem (hFA a ha) _)
      rw [e1, Finset.sum_union hdisj]
      have e2 : ∑ a ∈ C0, (D a N m : ℝ) = c := by
        rw [hc]; push_cast
        exact Finset.sum_congr rfl (fun a ha => by rw [D_of_dvd (hC0N a ha)])
      have e3 : ∑ a ∈ B, (D a N m : ℝ) = r := by
        rw [Finset.sum_congr rfl (fun b hb => by
          rw [D_forced hm1 (by have := hBK b hb; omega) (hBN b hb)])]
        simp [hBcard]
      rw [e2, e3]; push_cast; ring
    · intro a ha
      by_cases haA : a ∈ A
      · rw [Set.indicator_of_mem haA, hDU a ⟨haA, by exact_mod_cast ha⟩]; simp
      · exact Set.indicator_of_notMem haA _
  have hdiv : c + r = 2 ^ m * (c / 2 ^ m + 1) := by
    have hpm : 0 < 2 ^ m := by positivity
    have := Nat.mod_lt c hpm
    have := Nat.mod_add_div c (2 ^ m)
    rw [mul_add, mul_one, hr]; omega
  obtain ⟨z, hz⟩ := R_int A q p h0 N
  have hshift := R_shift A q N m
  obtain ⟨k, hk⟩ : ∃ k : ℕ, c + r = 2 ^ m * k := ⟨_, hdiv⟩
  rw [hsumD, hk, hz] at hshift
  set y : ℤ := z - q * k with hy
  have hRy : R A q (N + m) = 2 ^ m * y := by
    rw [hy]; push_cast at hshift ⊢; linarith only [hshift]
  obtain ⟨a0, ha0⟩ := hinf.nonempty
  have hRpos := R_pos A q hq ha0 (hpos a0 ha0) (N + m)
  have hypos : (0:ℝ) < y := by
    by_contra hneg; push_neg at hneg
    have : (2:ℝ) ^ m * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hy1 : (1:ℝ) ≤ y := by
    have : (0:ℤ) < y := by exact_mod_cast hypos
    exact_mod_cast (show (1:ℤ) ≤ y by omega)
  have hlow : (2:ℝ) ^ m ≤ R A q (N + m) := by
    rw [hRy]; nlinarith [(by positivity : (0:ℝ) < 2 ^ m)]
  -- upper bound
  set β : ℕ → ℝ := fun a => min 1 ((2:ℝ) ^ m / (2 ^ a - 1)) with hβ
  have hβnn : ∀ a, 0 ≤ β a := fun a =>
    le_min zero_le_one (div_nonneg (by positivity) (two_pow_sub_one_nonneg a))
  have hFzero : ∀ a ∉ F, (↑F : Set ℕ).indicator β a = 0 := fun a ha =>
    Set.indicator_of_notMem (by exact_mod_cast ha) _
  have hsF : Summable ((↑F : Set ℕ).indicator β) := summable_of_ne_finset_zero hFzero
  have hpt : ∀ a, A.indicator (fun a => w a (N + m)) a ≤
      (↑F : Set ℕ).indicator β a + 2 ^ m * U.indicator (fun a => w a N) a := by
    intro a
    by_cases haA : a ∈ A
    · rw [Set.indicator_of_mem haA]
      by_cases haF : a ∈ F
      · rw [Set.indicator_of_mem (show a ∈ (↑F : Set ℕ) by exact_mod_cast haF),
          Set.indicator_of_notMem (show a ∉ U from fun h => h.2 (by exact_mod_cast haF))]
        have hmod : (N + m) % a ≤ m := by
          rcases Finset.mem_union.mp haF with h | h
          · rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp (hC0N a h), zero_add, Nat.mod_mod]
            exact Nat.mod_le m a
          · rw [Nat.dvd_iff_mod_eq_zero.mp (hBN a h)]; omega
        simp only [mul_zero, add_zero, hβ]
        exact le_min (w_le_one a _) (w_le_of_mod_le hmod)
      · have haU : a ∈ U := ⟨haA, by exact_mod_cast haF⟩
        rw [Set.indicator_of_notMem (show a ∉ (↑F : Set ℕ) by exact_mod_cast haF),
          Set.indicator_of_mem haU, zero_add]
        have := w_shift a N m
        have : (0:ℝ) ≤ D a N m := by positivity
        linarith
    · rw [Set.indicator_of_notMem haA]
      exact add_nonneg (Set.indicator_nonneg (fun a _ => hβnn a) a)
        (mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => w_nonneg _ _) a))
  have htle := Summable.tsum_le_tsum hpt (summable_w A (N + m)) (hsF.add ((summable_w U N).mul_left _))
  rw [Summable.tsum_add hsF ((summable_w U N).mul_left _), tsum_mul_left, tsum_eq_sum hFzero] at htle
  have hFsum : ∑ a ∈ F, (↑F : Set ℕ).indicator β a ≤ m + 3 := by
    rw [Finset.sum_congr rfl (fun a ha => Set.indicator_of_mem (show a ∈ (↑F : Set ℕ) by exact_mod_cast ha) _)]
    exact sum_beta F m
  have hVlt : (2:ℝ) ^ m * V < 1 := by
    calc (2:ℝ) ^ m * V < 2 ^ m * δ := by gcongr
      _ = 1 := hδm
  have hup : R A q (N + m) < q * (m + 4) := by
    show (q:ℝ) * _ < _
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq
    have : ∑' a, A.indicator (fun a => w a (N + m)) a < m + 4 := by
      linarith only [htle, hFsum, hVlt]
    exact mul_lt_mul_of_pos_left this hqpos
  linarith only [hup, hlow, hmq]

/-- Erdős 257 for pairwise coprime `A` with convergent `∑_{n ∈ A} 1/n`. Known: P. Erdős,
*On the irrationality of certain series*, Math. Student 36 (1968), 222–226, Theorem (p. 222:
"Let `(n_i, n_j) = 1`, `∑ 1/n_i < ∞`. Then `∑ 1/(t^{n_i} - 1)` is irrational for every
`t ≥ 2`"; here `t = 2`). Erdős adds that coprimality can be dropped by "more complicated
arguments" whose details he does not give. The primes are pairwise coprime but `∑ 1/p`
diverges, so they are not a case of this statement. -/
theorem Opn.erdos_257_coprime_summable :
    ∀ A : Set ℕ, A.Infinite → A.Pairwise Nat.Coprime →
      Summable (fun n : A => (1 : ℝ) / n.1) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro A hinf hcop hsum
  have h0A : 0 ∉ A := by
    intro h0
    apply hinf
    refine (Set.toFinite ({0, 1} : Set ℕ)).subset ?_
    intro a ha
    by_cases ha0 : a = 0
    · simp [ha0]
    · have := (Nat.coprime_zero_left a).mp (hcop h0 ha (Ne.symm ha0))
      simp [this]
  have hpos : ∀ a ∈ A, 1 ≤ a := fun a ha =>
    Nat.pos_of_ne_zero (fun h => h0A (h ▸ ha))
  have hA : Summable (A.indicator fun a : ℕ => (1:ℝ) / a) :=
    summable_subtype_iff_indicator.mp hsum
  rintro ⟨x, hx⟩
  have e : (fun a => w a 0) = fun a : ℕ => (1:ℝ) / (2 ^ a - 1) := by
    funext a; simp [w]
  have hR0 : R A x.den 0 = x.num := by
    unfold R
    rw [e, ← tsum_subtype A (fun a : ℕ => (1:ℝ) / (2 ^ a - 1)), ← hx]
    have h1 := Rat.mul_den_eq_num x
    have h2 : ((x * x.den : ℚ) : ℝ) = ((x.num : ℚ) : ℝ) := by rw [h1]
    push_cast at h2
    linarith
  exact main_contra A hinf hcop hpos hA x.den x.den_pos x.num hR0
