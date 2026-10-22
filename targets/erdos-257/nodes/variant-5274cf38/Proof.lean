import Mathlib
import Nodes.«variant-5274cf38».Context

/- The divisor-counting function. -/
private def dd (n : ℕ) : ℕ := n.divisors.card

/- `b` times the "tail" `∑_{i ≥ 1} f(j+i) / 2^i`. -/
private noncomputable def Tail (f : ℕ → ℕ) (b : ℕ) (j : ℕ) : ℝ :=
  b * ∑' i : ℕ, (f (j + i + 1) : ℝ) / 2 ^ (i + 1)

/- The integer that the tail equals when the series is `a / b`. -/
private def Zint (f : ℕ → ℕ) (a : ℤ) (b : ℕ) (j : ℕ) : ℤ :=
  a * 2 ^ j - b * ∑ n ∈ Finset.range (j + 1), (f n : ℤ) * 2 ^ (j - n)

private lemma le_self_of_le_dd {f : ℕ → ℕ} (hf : ∀ n, f n ≤ dd n) (n : ℕ) : f n ≤ n :=
  (hf n).trans (Nat.card_divisors_le_self n)

private lemma summable_f_shift {f : ℕ → ℕ} (hf : ∀ n, f n ≤ dd n) (j : ℕ) :
    Summable (fun i : ℕ => (f (j + i + 1) : ℝ) / 2 ^ (i + 1)) := by
  have h : Summable (fun i : ℕ => ((j + 1 : ℝ) + i) * (1/2) ^ i) := by
    have h1 := (summable_geometric_two).mul_left (j+1 : ℝ)
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2 : ℝ))
      (by norm_num [abs_of_pos])
    simpa [add_mul] using h1.add h2
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h
  have : (f (j + i + 1) : ℝ) ≤ j + i + 1 := by exact_mod_cast le_self_of_le_dd hf _
  rw [div_eq_mul_inv, pow_succ, mul_inv, one_div, inv_pow]
  have : (0:ℝ) ≤ (2 ^ i)⁻¹ := by positivity
  nlinarith

private lemma summable_f {f : ℕ → ℕ} (hf : ∀ n, f n ≤ dd n) :
    Summable (fun n : ℕ => (f n : ℝ) / 2 ^ n) := by
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2 : ℝ))
    (by norm_num [abs_of_pos])
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h2
  have : (f i : ℝ) ≤ i := by exact_mod_cast le_self_of_le_dd hf _
  rw [div_eq_mul_inv, one_div, inv_pow, pow_one]
  have : (0:ℝ) ≤ (2 ^ i)⁻¹ := by positivity
  nlinarith

private lemma tail_pos {f : ℕ → ℕ} (hf : ∀ n, f n ≤ dd n) (hpos : ∀ j, ∃ i, 0 < f (j + i + 1))
    {b : ℕ} (hb : 0 < b) (j : ℕ) : 0 < Tail f b j := by
  unfold Tail
  apply mul_pos (by exact_mod_cast hb)
  obtain ⟨i, hi⟩ := hpos j
  apply (summable_f_shift hf j).tsum_pos (fun i => by positivity) i
  have : (0 : ℝ) < f (j + i + 1) := by exact_mod_cast hi
  positivity

private lemma tail_upper {f : ℕ → ℕ} (hf : ∀ n, f n ≤ dd n) (b j L : ℕ) :
    Tail f b j ≤ b * ∑ i ∈ Finset.range L, (f (j + i + 1) : ℝ) / 2 ^ (i + 1)
      + b * ((j + L + 2 : ℝ) / 2 ^ L) := by
  unfold Tail
  rw [← (summable_f_shift hf j).sum_add_tsum_nat_add L, mul_add]
  gcongr
  have hg1 : Summable (fun i : ℕ => (1/2 : ℝ) ^ i) := summable_geometric_two
  have hg2 : Summable (fun i : ℕ => (i : ℝ) * (1/2 : ℝ) ^ i) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2 : ℝ))
      (by norm_num [abs_of_pos])
  have key : ∑' i : ℕ, ((j + L + 1 : ℝ) / 2 ^ (L + 1) * (1/2) ^ i
      + 1 / 2 ^ (L + 1) * ((i : ℝ) * (1/2) ^ i)) = (j + L + 2 : ℝ) / 2 ^ L := by
    rw [(hg1.mul_left _).tsum_add (hg2.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_geometric_two, tsum_coe_mul_geometric_of_norm_lt_one (by norm_num [abs_of_pos])]
    rw [pow_succ]; field_simp; ring
  rw [← key]
  refine Summable.tsum_le_tsum (fun i => ?_)
    ((summable_nat_add_iff L).mpr (summable_f_shift hf j))
    ((hg1.mul_left _).add (hg2.mul_left _))
  have : (f (j + (i + L) + 1) : ℝ) ≤ j + L + 1 + i := by
    have := le_self_of_le_dd hf (j + (i + L) + 1)
    have : (f (j + (i + L) + 1) : ℝ) ≤ ((j + (i + L) + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  show (f (j + (i + L) + 1) : ℝ) / 2 ^ (i + L + 1) ≤ _
  rw [show (2:ℝ) ^ (i + L + 1) = 2 ^ (L+1) * 2 ^ i by ring, one_div_pow]
  rw [div_le_iff₀ (by positivity)]
  field_simp
  linarith

private lemma tsum_pnat_of_zero (f : ℕ → ℝ) (h0 : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n : ℕ, f n := by
  apply Function.Injective.tsum_eq PNat.coe_injective
  intro n hn
  have : n ≠ 0 := by rintro rfl; exact hn h0
  exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩

private lemma tail_eq_Zint {f : ℕ → ℕ} (hf : ∀ n, f n ≤ dd n) {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : ∑' n : ℕ, (f n : ℝ) / 2 ^ n = a / b) (j : ℕ) : Tail f b j = Zint f a b j := by
  have hsplit := (summable_f hf).sum_add_tsum_nat_add (j + 1)
  have htail : ∑' i : ℕ, (f (i + (j + 1)) : ℝ) / 2 ^ (i + (j + 1)) =
      (1 / 2 ^ j) * ∑' i : ℕ, (f (j + i + 1) : ℝ) / 2 ^ (i + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro i
    rw [show i + (j + 1) = j + i + 1 by ring,
      show (2:ℝ) ^ (j + i + 1) = 2 ^ j * 2 ^ (i + 1) by ring]
    field_simp
  rw [htail, h] at hsplit
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hT : Tail f b j = 2 ^ j * (a - b * ∑ n ∈ Finset.range (j + 1), (f n : ℝ) / 2 ^ n) := by
    unfold Tail
    field_simp at hsplit
    have : (2:ℝ) ^ j ≠ 0 := by positivity
    field_simp
    linear_combination hsplit
  rw [hT]
  unfold Zint
  push_cast
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl; intro n hn
    have hn' : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [pow_sub₀ _ (by norm_num) hn']
    field_simp

private lemma Zint_dvd (f : ℕ → ℕ) (a : ℤ) (b k m : ℕ) (hd : ∀ n, k < n → n ≤ k + m → 2 ^ m ∣ f n) :
    (2 : ℤ) ^ m ∣ Zint f a b (k + m) := by
  unfold Zint
  apply dvd_sub
  · exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  · apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro n hn
    have hn' : n ≤ k + m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    by_cases hnk : n ≤ k
    · exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
    · apply Dvd.dvd.mul_right
      exact_mod_cast hd n (by omega) hn'

private lemma dd_le_two_mul_small (n : ℕ) :
    dd n ≤ 2 * (n.divisors.filter (fun e => e * e ≤ n)).card := by
  unfold dd
  rw [← Finset.card_filter_add_card_filter_not (fun e => e * e ≤ n)]
  have : (n.divisors.filter (fun e => ¬ e * e ≤ n)).card ≤
      (n.divisors.filter (fun e => e * e ≤ n)).card := by
    apply Finset.card_le_card_of_injOn (fun e => n / e)
    · intro e he
      simp only [Finset.coe_filter, Nat.mem_divisors, not_le, Set.mem_setOf_eq] at he ⊢
      obtain ⟨⟨hd, hn⟩, hlt⟩ := he
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)
      refine ⟨⟨Nat.div_dvd_of_dvd hd, hn⟩, ?_⟩
      have h1 : n / e < e := (Nat.div_lt_iff_lt_mul hepos).mpr hlt
      calc n / e * (n / e) ≤ n / e * e := Nat.mul_le_mul_left _ h1.le
        _ = n := Nat.div_mul_cancel hd
    · intro e1 h1 e2 h2 h
      simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at h1 h2
      have := congrArg (fun x => n / x) h
      simp only at this
      rwa [Nat.div_div_self h1.1.1 h1.1.2, Nat.div_div_self h2.1.1 h2.1.2] at this
  omega

private lemma card_AP_dvd_le (r Q X e : ℕ) (hcop : Nat.Coprime r Q) :
    ((Finset.range X).filter (fun t => (e + 1) ∣ r + t * Q)).card ≤ X / (e + 1) + 1 := by
  set E := e + 1 with hE
  have hEpos : 0 < E := by omega
  have key : ∀ t1 ∈ (Finset.range X).filter (fun t => E ∣ r + t * Q),
      ∀ t2 ∈ (Finset.range X).filter (fun t => E ∣ r + t * Q), t1 / E = t2 / E → t1 ≤ t2 → t1 = t2 := by
    intro t1 h1 t2 h2 hq hle
    simp only [Finset.mem_filter, Finset.mem_range] at h1 h2
    have hcopE : Nat.Coprime E Q := by
      have hg1 : Nat.gcd E Q ∣ r + t1 * Q := (Nat.gcd_dvd_left E Q).trans h1.2
      have hg2 : Nat.gcd E Q ∣ t1 * Q := Dvd.dvd.mul_left (Nat.gcd_dvd_right E Q) _
      have hg3 : Nat.gcd E Q ∣ r := (Nat.dvd_add_left hg2).mp hg1
      have hg4 : Nat.gcd E Q ∣ Nat.gcd r Q := Nat.dvd_gcd hg3 (Nat.gcd_dvd_right E Q)
      rw [hcop] at hg4
      exact Nat.dvd_one.mp hg4
    have hd : E ∣ (t2 - t1) * Q := by
      have := Nat.dvd_sub h2.2 h1.2
      rwa [show r + t2 * Q - (r + t1 * Q) = (t2 - t1) * Q by rw [Nat.sub_mul]; omega] at this
    have hd2 : E ∣ t2 - t1 := hcopE.dvd_of_dvd_mul_right hd
    have hlt : t2 - t1 < E := by
      have e1 := Nat.div_add_mod t1 E
      have e2 := Nat.div_add_mod t2 E
      have m1 := Nat.mod_lt t1 hEpos
      have m2 := Nat.mod_lt t2 hEpos
      rw [hq] at e1
      omega
    have := Nat.eq_zero_of_dvd_of_lt hd2 hlt
    omega
  calc ((Finset.range X).filter (fun t => E ∣ r + t * Q)).card ≤ (Finset.range (X / E + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun t => t / E)
        · intro t ht
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht
          simp only [Finset.coe_range, Set.mem_Iio]
          have := Nat.div_le_div_right (c := E) ht.1.le
          omega
        · intro t1 h1 t2 h2 hq
          rcases le_total t1 t2 with h | h
          · exact key t1 h1 t2 h2 hq h
          · exact (key t2 h2 t1 h1 hq.symm h).symm
    _ = X / E + 1 := Finset.card_range _

private lemma sum_dd_AP_le (r Q X : ℕ) (hcop : Nat.Coprime r Q)
    (hX : ∀ t < X, r + t * Q ≤ X * X) :
    (∑ t ∈ Finset.range X, (dd (r + t * Q) : ℝ)) ≤ 2 * X * (2 + Real.log X) := by
  have hnat : ∑ t ∈ Finset.range X, dd (r + t * Q) ≤ 2 * ∑ e ∈ Finset.range X, (X / (e + 1) + 1) := by
    calc ∑ t ∈ Finset.range X, dd (r + t * Q)
        ≤ ∑ t ∈ Finset.range X, 2 * ((Finset.range X).filter (fun e => (e + 1) ∣ r + t * Q)).card := by
          apply Finset.sum_le_sum; intro t ht
          refine (dd_le_two_mul_small _).trans ?_
          apply Nat.mul_le_mul_left
          apply Finset.card_le_card_of_injOn (fun e => e - 1)
          · intro e he
            simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at he
            simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
            have hepos : 0 < e := Nat.pos_of_dvd_of_pos he.1.1 (Nat.pos_of_ne_zero he.1.2)
            have : e * e ≤ X * X := he.2.trans (hX t (by simpa using ht))
            have : e ≤ X := Nat.mul_self_le_mul_self_iff.mp this
            refine ⟨by omega, ?_⟩
            rw [Nat.sub_add_cancel hepos]; exact he.1.1
          · intro e1 h1 e2 h2 h
            simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_setOf_eq] at h1 h2
            have := Nat.pos_of_dvd_of_pos h1.1.1 (Nat.pos_of_ne_zero h1.1.2)
            have := Nat.pos_of_dvd_of_pos h2.1.1 (Nat.pos_of_ne_zero h2.1.2)
            simp only at h
            omega
      _ = 2 * ∑ e ∈ Finset.range X, ((Finset.range X).filter (fun t => (e + 1) ∣ r + t * Q)).card := by
          rw [← Finset.mul_sum]
          congr 1
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ 2 * ∑ e ∈ Finset.range X, (X / (e + 1) + 1) := by
          apply Nat.mul_le_mul_left
          exact Finset.sum_le_sum fun e _ => card_AP_dvd_le r Q X e hcop
  have hreal : ((∑ e ∈ Finset.range X, (X / (e + 1) + 1) : ℕ) : ℝ) ≤ X * (1 + Real.log X) + X := by
    push_cast
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    gcongr
    calc ∑ e ∈ Finset.range X, ((X / (e + 1) : ℕ) : ℝ) ≤ ∑ e ∈ Finset.range X, (X : ℝ) / (e + 1) := by
          apply Finset.sum_le_sum; intro e _
          have := Nat.cast_div_le (α := ℝ) (m := X) (n := e + 1)
          push_cast at this; exact this
      _ = X * (harmonic X : ℝ) := by
          rw [harmonic]; push_cast; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro e _; field_simp
      _ ≤ X * (1 + Real.log X) := by
          gcongr
          exact harmonic_le_one_add_log X
  have h1 : (∑ t ∈ Finset.range X, (dd (r + t * Q) : ℝ)) ≤
      2 * ((∑ e ∈ Finset.range X, (X / (e + 1) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

private lemma exists_param (b p A : ℕ) (hA : 1 ≤ A) :
    ∃ m : ℕ, b ≤ m ∧ p ≤ m ∧ 1 ≤ m ∧ 15 * A * m ^ 5 < 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 5 (r := (2:ℝ)) (by norm_num)
  have hA' : (0 : ℝ) < 1 / (15 * A) := by
    have : (1 : ℝ) ≤ A := by exact_mod_cast hA
    positivity
  have h2 := (h.eventually (gt_mem_nhds hA')).and
    (Filter.eventually_ge_atTop (max (max b p) 1))
  obtain ⟨m, hm, hmb⟩ := h2.exists
  refine ⟨m, le_of_max_le_left (le_of_max_le_left hmb),
    le_of_max_le_right (le_of_max_le_left hmb), le_of_max_le_right hmb, ?_⟩
  have hApos : (0 : ℝ) < 15 * A := by
    have : (1 : ℝ) ≤ A := by exact_mod_cast hA
    positivity
  have : (m : ℝ) ^ 5 < 1 / (15 * A) * 2 ^ m := by
    rwa [div_lt_iff₀ (by positivity)] at hm
  have : (15 * A * m ^ 5 : ℝ) < 2 ^ m := by
    calc (15 * A * m ^ 5 : ℝ) < 15 * A * (1 / (15 * A) * 2 ^ m) :=
          mul_lt_mul_of_pos_left this hApos
      _ = 2 ^ m := by field_simp
  exact_mod_cast this

private lemma idx_inj {m i j i' j' : ℕ} (hj : j < m) (hj' : j' < m) (h : i * m + j = i' * m + j') :
    i = i' ∧ j = j' := by
  rcases lt_trichotomy i i' with hi | hi | hi
  · exfalso
    have : (i + 1) * m ≤ i' * m := Nat.mul_le_mul_right _ hi
    nlinarith
  · subst hi; omega
  · exfalso
    have : (i' + 1) * m ≤ i * m := Nat.mul_le_mul_right _ hi
    nlinarith





/- Numerical facts about the parameters. -/
private lemma param_facts {b m A : ℕ} (hA : 1 ≤ A) (hbm : b ≤ m) (hm1 : 1 ≤ m)
    (hm : 15 * A * m ^ 5 < 2 ^ m) :
    let q := A * (m + m * m) * (m * m)
    m + 3 * q < 2 ^ m ∧ m + 3 * q ≤ 2 ^ q ∧ 8 * b ≤ 2 ^ q ∧
      2 * b * (3 + q) + 1 < 2 ^ m := by
  intro q
  have hq4 : q ≤ 2 * (A * m ^ 4) := by
    have : m + m * m ≤ 2 * (m * m) := by nlinarith
    calc q ≤ A * (2 * (m * m)) * (m * m) := by simp only [q]; gcongr
      _ = 2 * (A * m ^ 4) := by ring
  have hm5 : A * m ^ 4 ≤ A * m ^ 5 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm1 (by norm_num))
  have hm5' : m ≤ A * m ^ 5 := by
    calc m = 1 * m ^ 1 := by ring
      _ ≤ A * m ^ 5 := Nat.mul_le_mul hA (Nat.pow_le_pow_right hm1 (by norm_num))
  have hmq : m ≤ q := by
    have h1 : 1 ≤ m * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 : 1 ≤ A * (m + m * m) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc m ≤ A * (m + m * m) * 1 * m := by nlinarith
      _ ≤ A * (m + m * m) * (m * m) := by nlinarith
  have h2q : 2 ^ m ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hmq
  have e15 : 15 * A * m ^ 5 = 15 * (A * m ^ 5) := by ring
  refine ⟨by omega, by omega, by omega, ?_⟩
  have : b * (3 + q) ≤ m * (3 + 2 * (A * m ^ 4)) := Nat.mul_le_mul hbm (by omega)
  have : m * (3 + 2 * (A * m ^ 4)) = 3 * m + 2 * (A * m ^ 5) := by ring
  have : 2 * b * (3 + q) = 2 * (b * (3 + q)) := by ring
  omega

/- The averaging contradiction: the lower bounds `2^m ≤ Tail` along an arithmetic progression
are incompatible with the average size of the divisor function. -/
private lemma averaging_contra {f : ℕ → ℕ} (hf : ∀ n, f n ≤ dd n) {b m q Q c : ℕ} (hb : 0 < b) (hQpos : 0 < Q) (hcQ : c < Q)
    (hQle : Q ≤ 2 ^ q) (hA2 : m + 3 * q ≤ 2 ^ q) (hA3 : 8 * b ≤ 2 ^ q)
    (hA4 : 2 * b * (3 + q) + 1 < 2 ^ m)
    (hcop : ∀ i < 3 * q, Nat.Coprime (c + m + i + 1) Q)
    (hlow : ∀ t, (2 : ℝ) ^ m ≤ Tail f b (c + t * Q + m)) : False := by
  set L := 3 * q with hLdef
  set X := Q + m + L with hXdef
  -- numerical facts
  have hX1 : 1 ≤ X := by omega
  have hXpow : X ≤ 2 ^ (q + 1) := by rw [pow_succ]; omega
  have hLX : 2 * b * X ^ 2 ≤ 2 ^ L := by
    calc 2 * b * X ^ 2 ≤ 2 * b * (2 ^ (q + 1)) ^ 2 := by gcongr
      _ = 8 * b * (2 ^ q * 2 ^ q) := by ring
      _ ≤ 2 ^ q * (2 ^ q * 2 ^ q) := by gcongr
      _ = 2 ^ L := by rw [hLdef]; ring
  have hrange : ∀ t < X, c + t * Q < X * Q := by
    intro t ht
    have : (t + 1) * Q ≤ X * Q := Nat.mul_le_mul_right _ ht
    nlinarith
  have hXX : X * Q + m + L ≤ X * X := by
    have : X * X = X * Q + X * (m + L) := by rw [hXdef]; ring
    have : m + L ≤ X * (m + L) := Nat.le_mul_of_pos_left _ hX1
    omega
  -- upper bound for each t
  have hupt : ∀ t < X, Tail f b (c + t * Q + m) ≤
      b * ∑ i ∈ Finset.range L, (f (c + m + i + 1 + t * Q) : ℝ) / 2 ^ (i + 1)
        + b * ((2 * X ^ 2 : ℕ) / 2 ^ L : ℝ) := by
    intro t ht
    have h := tail_upper hf b (c + t * Q + m) L
    have e : ∀ i, c + t * Q + m + i + 1 = c + m + i + 1 + t * Q := fun i => by ring
    simp only [e] at h
    refine h.trans (add_le_add le_rfl ?_)
    gcongr
    have := hrange t ht
    have h2 : c + t * Q + m + L + 2 ≤ 2 * X ^ 2 := by nlinarith
    exact_mod_cast h2
  have hgeom : ∀ L : ℕ, ∑ i ∈ Finset.range L, (1 / 2 : ℝ) ^ (i + 1) ≤ 1 := by
    intro L
    have : ∑ i ∈ Finset.range L, (1 / 2 : ℝ) ^ (i + 1) = 1 - (1 / 2) ^ L := by
      induction L with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; ring
    rw [this]; linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) L]
  set B : ℝ := 2 * X * (2 + Real.log X) with hBdef
  have hF : ∀ i ∈ Finset.range L, (∑ t ∈ Finset.range X, (f (c + m + i + 1 + t * Q) : ℝ)) ≤ B := by
    intro i hi
    refine (Finset.sum_le_sum fun t _ => (by exact_mod_cast hf _ :
      (f (c + m + i + 1 + t * Q) : ℝ) ≤ dd (c + m + i + 1 + t * Q))).trans ?_
    apply sum_dd_AP_le _ _ _ (hcop i (by simpa using hi))
    intro t ht
    have := hrange t ht
    have : i < L := by simpa using hi
    omega
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX1)
    positivity
  have hmain : (X : ℝ) * 2 ^ m ≤ b * B + X := by
    calc (X : ℝ) * 2 ^ m = ∑ t ∈ Finset.range X, (2 : ℝ) ^ m := by simp
      _ ≤ ∑ t ∈ Finset.range X, Tail f b (c + t * Q + m) := Finset.sum_le_sum fun t _ => hlow t
      _ ≤ ∑ t ∈ Finset.range X, (b * ∑ i ∈ Finset.range L, (f (c + m + i + 1 + t * Q) : ℝ) / 2 ^ (i + 1)
            + b * ((2 * X ^ 2 : ℕ) / 2 ^ L : ℝ)) :=
          Finset.sum_le_sum fun t ht => hupt t (by simpa using ht)
      _ = b * ∑ i ∈ Finset.range L, (∑ t ∈ Finset.range X, (f (c + m + i + 1 + t * Q) : ℝ)) * (1 / 2) ^ (i + 1)
            + X * (b * ((2 * X ^ 2 : ℕ) / 2 ^ L : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_mul, div_eq_mul_inv,
            inv_pow, one_mul]
      _ ≤ b * ∑ i ∈ Finset.range L, B * (1 / 2) ^ (i + 1) + X * 1 := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_right (hF i hi) (by positivity)
          · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            rw [← mul_div_assoc, div_le_one (by positivity)]
            have h1 : b * (2 * X ^ 2) ≤ 2 ^ L := by
              calc b * (2 * X ^ 2) = 2 * b * X ^ 2 := by ring
                _ ≤ 2 ^ L := hLX
            exact_mod_cast h1
      _ ≤ b * B + X := by
          rw [← Finset.mul_sum, mul_one]
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          calc B * ∑ i ∈ Finset.range L, (1 / 2 : ℝ) ^ (i + 1) ≤ B * 1 :=
                mul_le_mul_of_nonneg_left (hgeom L) hB0
            _ = B := mul_one B
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have h2m : (2 : ℝ) ^ m ≤ 2 * b * (2 + Real.log X) + 1 := by
    have : (X : ℝ) * 2 ^ m ≤ X * (2 * b * (2 + Real.log X) + 1) := by
      rw [hBdef] at hmain; nlinarith
    exact le_of_mul_le_mul_left this hXpos
  have hlogX : Real.log X ≤ q + 1 := by
    calc Real.log X ≤ Real.log ((2 : ℝ) ^ (q + 1)) :=
          Real.log_le_log hXpos (by exact_mod_cast hXpow)
      _ = (q + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (q + 1) * 1 := by
          gcongr
          linarith [Real.log_two_lt_d9]
      _ = q + 1 := mul_one _
  have hA4' : (2 * b * (3 + q) + 1 : ℝ) < 2 ^ m := by exact_mod_cast hA4
  have : (2 * b * (2 + Real.log X) + 1 : ℝ) ≤ 2 * b * (3 + q) + 1 := by
    have : (0 : ℝ) ≤ b := by positivity
    nlinarith
  linarith


/- Abstract irrationality criterion: if `f ≤ d`, the tails of `∑ f(n)/2^n` never vanish, and
`f(n)` is divisible by `2^#S` whenever `S` is a set of primes larger than `p` each dividing `n`
exactly to the power `A - 1`, then `∑ f(n)/2^n` is irrational. -/
private theorem irrational_series {f : ℕ → ℕ} (hf : ∀ n, f n ≤ dd n)
    (hpos : ∀ j, ∃ i, 0 < f (j + i + 1)) (p A : ℕ) (hA : 2 ≤ A)
    (hdiv : ∀ n, n ≠ 0 → ∀ S : Finset ℕ,
      (∀ q ∈ S, q.Prime ∧ p < q ∧ q ^ (A - 1) ∣ n ∧ ¬ q ^ A ∣ n) → 2 ^ S.card ∣ f n) :
    Irrational (∑' n : ℕ, (f n : ℝ) / 2 ^ n) := by
  rintro ⟨qr, hq⟩
  set a : ℤ := qr.num
  set b : ℕ := qr.den
  have hb : 0 < b := qr.pos
  have hx : ∑' n : ℕ, (f n : ℝ) / 2 ^ n = a / b := by
    rw [← hq]; exact Rat.cast_def qr
  have hT : ∀ j, Tail f b j = Zint f a b j := tail_eq_Zint hf hb hx
  obtain ⟨m, hbm, hpm, hm1, hm⟩ := exists_param b p A (by omega)
  obtain ⟨hA1, hA2, hA3, hA4⟩ := param_facts (by omega) hbm hm1 hm
  set q := A * (m + m * m) * (m * m) with hqdef
  have hbert : ∀ e : ℕ, ∃ p, p.Prime ∧ 2 ^ e < p ∧ p ≤ 2 * 2 ^ e :=
    fun e => Nat.exists_prime_lt_and_le_two_mul _ (by positivity)
  choose P hPp hPlo hPhi using hbert
  have hPmono : ∀ e e', e < e' → P e < P e' := by
    intro e e' h
    calc P e ≤ 2 * 2 ^ e := hPhi e
      _ = 2 ^ (e + 1) := by ring
      _ ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) h
      _ < P e' := hPlo e'
  have hPinj : ∀ e e', P e = P e' → e = e' := by
    intro e e' h
    rcases lt_trichotomy e e' with h' | h' | h'
    · exact absurd h (hPmono _ _ h').ne
    · exact h'
    · exact absurd h (hPmono _ _ h').ne'
  set pr : ℕ × ℕ → ℕ := fun ij => P (m + ij.1 * m + ij.2) with hprdef
  set S : Finset (ℕ × ℕ) := Finset.range m ×ˢ Finset.range m with hSdef
  have hprp : ∀ ij, (pr ij).Prime := fun ij => hPp _
  have hprlo : ∀ ij, 2 ^ m < pr ij := by
    intro ij
    calc 2 ^ m ≤ 2 ^ (m + ij.1 * m + ij.2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < pr ij := hPlo _
  have hprhi : ∀ ij ∈ S, pr ij ≤ 2 ^ (m + m * m) := by
    intro ij hij
    simp only [hSdef, Finset.mem_product, Finset.mem_range] at hij
    have : ij.1 * m + ij.2 + 1 ≤ m * m := by
      have : (ij.1 + 1) * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    calc pr ij ≤ 2 * 2 ^ (m + ij.1 * m + ij.2) := hPhi _
      _ = 2 ^ (m + ij.1 * m + ij.2 + 1) := by ring
      _ ≤ 2 ^ (m + m * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinj : Set.InjOn pr (S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    simp only [hSdef, Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hx hy
    have h1 := hPinj _ _ hxy
    have h2 : x.1 * m + x.2 = y.1 * m + y.2 := by omega
    obtain ⟨e1, e2⟩ := idx_inj hx.2 hy.2 h2
    exact Prod.ext e1 e2
  set Q : ℕ := ∏ ij ∈ S, pr ij ^ A with hQdef
  have hQpos : 0 < Q := Finset.prod_pos (fun ij _ => pow_pos (hprp ij).pos A)
  have hQle : Q ≤ 2 ^ q := by
    calc Q ≤ ((2 ^ (m + m * m)) ^ A) ^ S.card := by
          apply Finset.prod_le_pow_card
          intro ij hij
          exact Nat.pow_le_pow_left (hprhi ij hij) A
      _ = 2 ^ q := by
          rw [hSdef, Finset.card_product, Finset.card_range, ← pow_mul, ← pow_mul, hqdef]
          congr 1; ring
  set L := 3 * q with hLdef
  have hdvdQ : ∀ ij ∈ S, pr ij ^ A ∣ Q := fun ij hij => Finset.dvd_prod_of_mem _ hij
  -- Chinese remainder theorem
  have hs : ∀ ij ∈ S, pr ij ^ A ≠ 0 := fun ij _ => (pow_pos (hprp ij).pos A).ne'
  have pp : Set.Pairwise (S : Set (ℕ × ℕ)) (Function.onFun Nat.Coprime fun ij => pr ij ^ A) := by
    intro x hx y hy hxy
    exact Nat.Coprime.pow A A ((Nat.coprime_primes (hprp x) (hprp y)).2
      (fun h => hxy (hinj hx hy h)))
  set crt := Nat.chineseRemainderOfFinset (fun ij => pr ij ^ A + pr ij ^ (A - 1) - (ij.1 + 1))
    (fun ij => pr ij ^ A) S hs pp
  set c : ℕ := crt.1
  have hc : ∀ ij ∈ S, c ≡ pr ij ^ A + pr ij ^ (A - 1) - (ij.1 + 1) [MOD pr ij ^ A] := crt.2
  have hcQ : c < Q := Nat.chineseRemainderOfFinset_lt_prod _ _ hs pp
  -- the key congruence
  have hk : ∀ t, ∀ ij ∈ S, c + t * Q + (ij.1 + 1) ≡ pr ij ^ (A - 1) [MOD pr ij ^ A] := by
    intro t ij hij
    obtain ⟨R, hR⟩ := hdvdQ ij hij
    have hi : ij.1 < m := by
      simp only [hSdef, Finset.mem_product, Finset.mem_range] at hij; exact hij.1
    have hp := hprlo ij
    have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
    have hpp : pr ij ≤ pr ij ^ (A - 1) := Nat.le_self_pow (by omega) _
    have e1 : c + t * Q ≡ c [MOD pr ij ^ A] := by
      rw [hR, show t * (pr ij ^ A * R) = pr ij ^ A * (t * R) by ring]
      exact Nat.add_mul_mod_self_left _ _ _
    have e2 := (e1.trans (hc ij hij)).add_right (ij.1 + 1)
    rw [Nat.sub_add_cancel (by omega)] at e2
    refine e2.trans ?_
    exact Nat.add_mod_left _ _
  -- forced divisibility
  have hforced : ∀ t, ∀ n, c + t * Q < n → n ≤ c + t * Q + m → 2 ^ m ∣ f n := by
    intro t n hn1 hn2
    obtain ⟨i, rfl⟩ : ∃ i, n = c + t * Q + (i + 1) := ⟨n - (c + t * Q) - 1, by omega⟩
    have hi : i < m := by omega
    have hcard : ((Finset.range m).image (fun j => pr (i, j))).card = m := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro j hj j' hj' h
      have := hinj (by simp [hSdef, hi, (by simpa using hj : j < m)])
        (by simp [hSdef, hi, (by simpa using hj' : j' < m)]) h
      simpa using this
    rw [← hcard]
    apply hdiv _ (by omega)
    intro p' hp'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp'
    have hij : (i, j) ∈ S := by simp [hSdef, hi, (by simpa using hj : j < m)]
    have h := hk t (i, j) hij
    have hpp := hprp (i, j)
    have hlo := hprlo (i, j)
    have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
    refine ⟨hpp, by omega, (h.dvd_iff (pow_dvd_pow _ (by omega))).2 dvd_rfl, ?_⟩
    rw [h.dvd_iff dvd_rfl]
    intro hd
    have h1 := Nat.le_of_dvd (pow_pos hpp.pos _) hd
    have h2 : pr (i, j) ^ (A - 1) < pr (i, j) ^ A :=
      Nat.pow_lt_pow_right hpp.one_lt (by omega)
    omega
  -- coprimality
  have hcop : ∀ i < L, Nat.Coprime (c + m + i + 1) Q := by
    intro i hi
    apply Nat.Coprime.prod_right
    intro ij hij
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hprp ij)]
    intro hd
    have hi0 : ij.1 < m := by
      simp only [hSdef, Finset.mem_product, Finset.mem_range] at hij; exact hij.1
    have h1 : pr ij ∣ c + 0 * Q + (ij.1 + 1) :=
      ((hk 0 ij hij).dvd_iff (dvd_pow_self _ (by omega))).2 (dvd_pow_self _ (by omega))
    have h2 : c + m + i + 1 = (c + 0 * Q + (ij.1 + 1)) + (m + i - ij.1) := by omega
    rw [h2] at hd
    have h3 := (Nat.dvd_add_right h1).mp hd
    have h4 := Nat.le_of_dvd (by omega) h3
    have := hprlo ij
    omega
  -- lower bound
  have hlow : ∀ t, (2 : ℝ) ^ m ≤ Tail f b (c + t * Q + m) := by
    intro t
    have hd := Zint_dvd f a b (c + t * Q) m (hforced t)
    have hpos := tail_pos hf hpos hb (c + t * Q + m)
    rw [hT] at hpos ⊢
    have hpos' : 0 < Zint f a b (c + t * Q + m) := by exact_mod_cast hpos
    have := Int.le_of_dvd hpos' hd
    exact_mod_cast this
  exact averaging_contra hf hb hQpos hcQ hQle hA2 hA3 hA4 hcop hlow




/- `fB B u n = #{e ∣ n : u * e ∈ B}`; the case `u = 1` is `f_B`. -/
private noncomputable def fB (B : Set ℕ) (u n : ℕ) : ℕ := (@Finset.filter ℕ (fun e => u * e ∈ B) (fun e => Classical.propDecidable (u * e ∈ B)) n.divisors).card


private lemma mem_add_mul {B : Set ℕ} {p : ℕ} (hper : ∀ n, n ∈ B ↔ n + p ∈ B) (n k : ℕ) : n ∈ B ↔ n + k * p ∈ B := by
  induction k with
  | zero => simp
  | succ k ih => rw [ih, hper, add_mul, one_mul, add_assoc]

private lemma mem_iff_of_modEq {B : Set ℕ} {p : ℕ} (hper : ∀ n, n ∈ B ↔ n + p ∈ B) {x y : ℕ} (h : x ≡ y [MOD p]) :
    x ∈ B ↔ y ∈ B := by
  have key : ∀ z, z ∈ B ↔ z % p ∈ B := by
    intro z
    conv_lhs => rw [← Nat.mod_add_div' z p]
    exact (mem_add_mul hper _ _).symm
  rw [key x, key y, h]

private lemma fB_le_dd (B : Set ℕ) (n : ℕ) : fB B 1 n ≤ dd n := by
  classical
  unfold fB dd; exact Finset.card_filter_le _ _

private lemma divisors_prime_pow_mul {q r : ℕ} (hq : q.Prime) (hr : ¬ q ∣ r) (a : ℕ) :
    (q ^ a * r).divisors = ((Finset.range (a + 1)) ×ˢ r.divisors).image (fun x => q ^ x.1 * x.2) := by
  have hr0 : r ≠ 0 := by rintro rfl; exact hr (dvd_zero q)
  have hn0 : q ^ a * r ≠ 0 := mul_ne_zero (pow_ne_zero _ hq.ne_zero) hr0
  ext d
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨hd, -⟩
    obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hd
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hq).1 hy
    exact ⟨k, z, ⟨by omega, hz, hr0⟩, rfl⟩
  · rintro ⟨k, e, ⟨hk, he, -⟩, rfl⟩
    exact ⟨mul_dvd_mul (pow_dvd_pow q (by omega)) he, hn0⟩

private lemma injOn_prime_pow_mul {q r : ℕ} (hq : q.Prime) (hr : ¬ q ∣ r) (a : ℕ) :
    Set.InjOn (fun x : ℕ × ℕ => q ^ x.1 * x.2) ((Finset.range (a + 1)) ×ˢ r.divisors : Finset _) := by
  rintro ⟨k, e⟩ hx ⟨k', e'⟩ hy h
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, Finset.mem_coe,
    Nat.mem_divisors] at hx hy h
  have he : ¬ q ∣ e := fun h' => hr (h'.trans hx.2.1)
  have he' : ¬ q ∣ e' := fun h' => hr (h'.trans hy.2.1)
  have he0 : e ≠ 0 := by rintro rfl; exact he (dvd_zero q)
  have he0' : e' ≠ 0 := by rintro rfl; exact he' (dvd_zero q)
  have hfac := congrArg (fun n => n.factorization q) h
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) he0,
    Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) he0'] at hfac
  simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hq.factorization_self, mul_one, Nat.factorization_eq_zero_of_not_dvd he,
    Nat.factorization_eq_zero_of_not_dvd he', add_zero] at hfac
  subst hfac
  have := Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos k) h
  simp [this]

private lemma fB_prime_pow_mul {B : Set ℕ} {q r : ℕ} (hq : q.Prime) (hr : ¬ q ∣ r) (a u : ℕ) :
    fB B u (q ^ a * r) = ∑ k ∈ Finset.range (a + 1), fB B (u * q ^ k) r := by
  classical
  unfold fB
  rw [divisors_prime_pow_mul hq hr, Finset.card_filter, Finset.sum_image (injOn_prime_pow_mul hq hr a),
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mul_assoc]

private lemma fB_periodic {B : Set ℕ} {p : ℕ} (hper : ∀ n, n ∈ B ↔ n + p ∈ B) {q o : ℕ} (hqo : q ^ o ≡ 1 [MOD p])
    (u k r : ℕ) : fB B (u * q ^ (o + k)) r = fB B (u * q ^ k) r := by
  classical
  unfold fB
  congr 1
  apply Finset.filter_congr
  intro e _
  apply mem_iff_of_modEq hper
  have : u * q ^ (o + k) * e = (u * q ^ k * e) * q ^ o := by ring
  rw [this]
  calc u * q ^ k * e * q ^ o ≡ u * q ^ k * e * 1 [MOD p] := hqo.mul_left _
    _ = u * q ^ k * e := mul_one _

/- If the primes in `S` are coprime to `p` and each divides `n` exactly to the power
`2 φ(p) - 1`, then `2 ^ #S ∣ fB B u n`. -/
private lemma two_pow_dvd_fB {B : Set ℕ} {p : ℕ} (hp : 0 < p) (hper : ∀ n, n ∈ B ↔ n + p ∈ B) (S : Finset ℕ) :
    ∀ u n, n ≠ 0 → (∀ q ∈ S, q.Prime ∧ q.Coprime p ∧ q ^ (2 * p.totient - 1) ∣ n ∧
      ¬ q ^ (2 * p.totient) ∣ n) → 2 ^ S.card ∣ fB B u n := by
  have ho : 0 < p.totient := Nat.totient_pos.mpr hp
  set o := p.totient with hodef
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert q S hqS ih =>
    intro u n hn hS
    obtain ⟨hqp, hcop, hdvd, hndvd⟩ := hS q (Finset.mem_insert_self _ _)
    obtain ⟨r, rfl⟩ := hdvd
    have hr : ¬ q ∣ r := by
      rintro ⟨s, rfl⟩
      apply hndvd
      have e : q ^ (2 * o) = q ^ (2 * o - 1) * q := by
        rw [← pow_succ]; congr 1; omega
      rw [e, ← mul_assoc]
      exact dvd_mul_right _ _
    have hr0 : r ≠ 0 := by rintro rfl; exact hr (dvd_zero q)
    have hqo : q ^ o ≡ 1 [MOD p] := Nat.ModEq.pow_totient hcop
    have hsub : ∀ k, 2 ^ S.card ∣ fB B (u * q ^ k) r := by
      intro k
      apply ih _ r hr0
      intro q' hq'
      obtain ⟨hq'p, hcop', hdvd', hndvd'⟩ := hS q' (Finset.mem_insert_of_mem hq')
      have hne : q' ≠ q := by rintro rfl; exact hqS hq'
      have hc : Nat.Coprime (q' ^ (2 * o - 1)) (q ^ (2 * o - 1)) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes hq'p hqp).2 hne)
      refine ⟨hq'p, hcop', hc.dvd_of_dvd_mul_left hdvd', fun h => hndvd' ?_⟩
      exact h.trans (dvd_mul_left _ _)
    rw [fB_prime_pow_mul hqp hr, Finset.card_insert_of_notMem hqS, pow_succ,
      show 2 * o - 1 + 1 = o + o by omega, Finset.sum_range_add]
    simp only [fB_periodic hper hqo]
    rw [← two_mul, mul_comm 2]
    exact mul_dvd_mul (Finset.dvd_sum fun k _ => hsub k) dvd_rfl

private lemma fB_pos_tail {B : Set ℕ} {p : ℕ} (hp : 0 < p) (hper : ∀ n, n ∈ B ↔ n + p ∈ B) (hB : B.Nonempty) (j : ℕ) :
    ∃ i, 0 < fB B 1 (j + i + 1) := by
  classical
  obtain ⟨e0, he0⟩ := hB
  have he1 : e0 + p ∈ B := (hper e0).1 he0
  set e1 := e0 + p
  have h1 : 1 ≤ e1 := by omega
  refine ⟨e1 * (j + 1) - j - 1, ?_⟩
  have hle : j + 1 ≤ e1 * (j + 1) := Nat.le_mul_of_pos_left _ h1
  rw [show j + (e1 * (j + 1) - j - 1) + 1 = e1 * (j + 1) by omega]
  unfold fB
  apply Finset.card_pos.mpr
  refine ⟨e1, ?_⟩
  simp only [Finset.mem_filter, Nat.mem_divisors, one_mul]
  exact ⟨⟨dvd_mul_right _ _, by positivity⟩, he1⟩

/- Lambert series identity: `∑_{n ∈ B} 1/(2^n - 1) = ∑_n f_B(n) / 2^n`. -/
private lemma lambert_B (B : Set ℕ) :
    ∑' n : B, (1 : ℝ) / (2 ^ n.1 - 1) = ∑' n : ℕ, (fB B 1 n : ℝ) / 2 ^ n := by
  classical
  set r : ℝ := 1 / 2 with hr
  have hr1 : ‖r‖ < 1 := by norm_num [hr, abs_of_pos]
  set H : ℕ+ × ℕ+ → ℝ := fun x => if (x.1 : ℕ) ∈ B then r ^ ((x.1 : ℕ) * x.2) else 0 with hHdef
  have hsum0 := summable_prod_mul_pow (𝕜 := ℝ) 0 hr1
  have hH : Summable H := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hsum0
    · simp only [H]; split_ifs <;> positivity
    · simp only [H, pow_zero, one_mul]; split_ifs
      · exact le_rfl
      · positivity
  have hgeo : ∀ d : ℕ+, ∑' c : ℕ+, r ^ ((d : ℕ) * c) = 1 / (2 ^ (d : ℕ) - 1) := by
    intro d
    have hlt : r ^ (d : ℕ) < 1 := pow_lt_one₀ (by norm_num [hr]) (by norm_num [hr]) d.ne_zero
    rw [tsum_pnat_eq_tsum_succ (f := fun c => r ^ ((d : ℕ) * c))]
    simp only [pow_mul, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity) hlt]
    have h2 : (1:ℝ) < 2 ^ (d : ℕ) := one_lt_pow₀ (by norm_num) d.ne_zero
    rw [hr, one_div_pow]
    field_simp
  have hA : ∑' n : B, (1 : ℝ) / (2 ^ n.1 - 1) = ∑' d : ℕ+, ∑' c : ℕ+, H (d, c) := by
    rw [tsum_subtype B (fun n => (1 : ℝ) / (2 ^ n - 1))]
    rw [← tsum_pnat_of_zero _ (by simp)]
    apply tsum_congr; intro d
    by_cases hd : (d : ℕ) ∈ B
    · simp only [Set.indicator_of_mem hd, H, if_pos hd]
      exact (hgeo d).symm
    · simp [H, hd]
  have hC : ∑' x : ℕ+ × ℕ+, H x = ∑' n : ℕ+, (fB B 1 n : ℝ) * r ^ (n : ℕ) := by
    rw [← _root_.sigmaAntidiagonalEquivProd.tsum_eq]
    have hs : Summable (fun c => H (_root_.sigmaAntidiagonalEquivProd c)) :=
      (_root_.sigmaAntidiagonalEquivProd.summable_iff).2 hH
    rw [hs.tsum_sigma]
    apply tsum_congr; intro n
    rw [tsum_fintype]
    have key : ∀ b : (n : ℕ).divisorsAntidiagonal,
        H (_root_.sigmaAntidiagonalEquivProd ⟨n, b⟩) =
          (fun x : ℕ × ℕ => if x.1 ∈ B then r ^ (n : ℕ) else 0) b.1 := by
      intro b
      have hb := (Nat.mem_divisorsAntidiagonal.mp b.2).1
      simp [H, _root_.sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, hb]
    simp_rw [key]
    rw [Finset.sum_coe_sort ((n : ℕ).divisorsAntidiagonal)
      (fun x : ℕ × ℕ => if x.1 ∈ B then r ^ (n : ℕ) else 0)]
    rw [Nat.sum_divisorsAntidiagonal (fun a _ => if a ∈ B then r ^ (n : ℕ) else 0)]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    unfold fB
    simp only [one_mul]
  rw [hA, ← hH.tsum_prod, hC, ← tsum_pnat_of_zero _ (by simp [fB])]
  apply tsum_congr; intro n
  simp [hr, div_eq_mul_inv]



/- Luca–Tachiya (IJNT 2014, Thm 1.1) for 0/1 sequences at q = 2: a nonempty purely periodic set
`B ⊆ ℕ` has an irrational Mersenne reciprocal sum. (`0 ∈ B` contributes `1/0 = 0` in Lean.) -/
private theorem pp_irr : ∀ B : Set ℕ, B.Nonempty → (∃ p : ℕ, 0 < p ∧ ∀ n, n ∈ B ↔ n + p ∈ B) →
      Irrational (∑' n : B, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  rintro B hB ⟨p, hp, hper⟩
  rw [lambert_B]
  apply irrational_series (fun n => fB_le_dd B n)
    (fB_pos_tail hp hper hB) p (2 * p.totient)
    (by have := Nat.totient_pos.mpr hp; omega)
  intro n hn S hS
  apply two_pow_dvd_fB hp hper S 1 n hn
  intro q hq
  obtain ⟨hqp, hpq, h1, h2⟩ := hS q hq
  exact ⟨hqp, (Nat.Prime.coprime_iff_not_dvd hqp).2
    (fun h => absurd (Nat.le_of_dvd hp h) (by omega)), h1, h2⟩

/-- Erdős 257 for every infinite `A` whose indicator is eventually periodic (for example any
arithmetic progression, the odd numbers, any union of residue classes, changed in finitely many
places). Known: F. Luca and Y. Tachiya, *Irrationality of Lambert series associated with a
periodic sequence*, Int. J. Number Theory 10 (2014), 623–636, Theorem 1.1 (restated as Theorem A,
RIMS Kôkyûroku 2014 (2017), p. 139): `∑ a(n)/(q^n - 1)` is irrational for every purely periodic
integer sequence `a`, not identically zero, and every integer `|q| > 1`. An eventually periodic
infinite `A` differs from a nonempty purely periodic set in finitely many places, which changes
the sum by a rational number. -/
theorem Opn.erdos_257_eventually_periodic :
    ∀ A : Set ℕ, A.Infinite →
      (∃ p N : ℕ, 0 < p ∧ ∀ n, N ≤ n → (n ∈ A ↔ n + p ∈ A)) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  have hper : ∀ B : Set ℕ, B.Nonempty → (∃ p : ℕ, 0 < p ∧ ∀ n, n ∈ B ↔ n + p ∈ B) →
      Irrational (∑' n : B, (1 : ℝ) / (2 ^ n.1 - 1)) := by
    exact pp_irr
  intro A hA ⟨p, N, hp, hAper⟩
  classical
  set f : ℕ → ℝ := fun n => (1 : ℝ) / (2 ^ n - 1) with hf
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) (fun n => ?_) (fun n => ?_)
      ((summable_geometric_two).mul_left 2)
    · have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      exact div_nonneg zero_le_one (by linarith)
    · rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [hf]
      · have h2 : (2 : ℝ) ≤ 2 ^ n := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
        have hpos : (0 : ℝ) < 2 ^ n - 1 := by linarith
        simp only [hf]
        rw [div_le_iff₀ hpos, one_div_pow, mul_assoc, mul_comm ((1:ℝ) / 2 ^ n), mul_one_div,
          mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith
  have hiter : ∀ k n, N ≤ n → (n ∈ A ↔ n + p * k ∈ A) := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [ih n hn, hAper (n + p * k) (by omega)]
      rw [show n + p * k + p = n + p * (k + 1) by ring]
  let B : Set ℕ := {n | n + p * N ∈ A}
  have hpN : N ≤ p * N := Nat.le_mul_of_pos_left N hp
  have hBper : ∀ n, n ∈ B ↔ n + p ∈ B := by
    intro n
    show n + p * N ∈ A ↔ n + p + p * N ∈ A
    rw [hAper (n + p * N) (by omega), show n + p * N + p = n + p + p * N by ring]
  have hAB : ∀ n, N ≤ n → (n ∈ A ↔ n ∈ B) := fun n hn => hiter N n hn
  have hBne : B.Nonempty := by
    obtain ⟨m, hm, hmN⟩ := hA.exists_gt N
    exact ⟨m, (hAB m hmN.le).1 hm⟩
  have hB := hper B hBne ⟨p, hp, hBper⟩
  have h1 := hfs.indicator A
  have h2 := hfs.indicator B
  have hsub := h1.tsum_sub h2
  have hfin : ∑' n, (A.indicator f n - B.indicator f n) =
      ∑ n ∈ Finset.range N, (A.indicator f n - B.indicator f n) := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp only [Set.indicator_apply]
    by_cases hnA : n ∈ A
    · simp [hnA, (hAB n hn).1 hnA]
    · have : n ∉ B := fun h => hnA ((hAB n hn).2 h)
      simp [hnA, this]
  have hrat : ∑ n ∈ Finset.range N, (A.indicator f n - B.indicator f n) =
      ((∑ n ∈ Finset.range N, ((if n ∈ A then (1 : ℚ) / (2 ^ n - 1) else 0) -
        (if n ∈ B then (1 : ℚ) / (2 ^ n - 1) else 0)) : ℚ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [Set.indicator_apply, hf]
    split_ifs <;> push_cast <;> ring
  have key : ∑' n : A, f n = ∑' n : B, f n + ((∑ n ∈ Finset.range N,
      ((if n ∈ A then (1 : ℚ) / (2 ^ n - 1) else 0) -
        (if n ∈ B then (1 : ℚ) / (2 ^ n - 1) else 0)) : ℚ) : ℝ) := by
    rw [tsum_subtype A f, tsum_subtype B f, ← hrat, ← hfin, hsub]
    ring
  obtain ⟨q, hq⟩ : ∃ q : ℚ, ∑' n : A, f n = ∑' n : B, f n + (q : ℝ) := ⟨_, key⟩
  show Irrational (∑' n : A, f n)
  rw [hq]
  rintro ⟨r, hr⟩
  exact hB ⟨r - q, by push_cast; linarith⟩

