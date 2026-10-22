import Mathlib
import Nodes.«variant-2f5236aa».Context

/- The divisor-counting function. -/
private def dd (n : ℕ) : ℕ := n.divisors.card

/- `b` times the "tail" `∑_{i ≥ 1} d(j+i) / 2^i`. -/
private noncomputable def Tail (b : ℕ) (j : ℕ) : ℝ := b * ∑' i : ℕ, (dd (j + i + 1) : ℝ) / 2 ^ (i + 1)

/- The integer that the tail equals when the series is `a / b`. -/
private def Zint (a : ℤ) (b : ℕ) (j : ℕ) : ℤ :=
  a * 2 ^ j - b * ∑ n ∈ Finset.range (j + 1), (dd n : ℤ) * 2 ^ (j - n)

private lemma dd_le (n : ℕ) : dd n ≤ n := Nat.card_divisors_le_self n

private lemma dd_pos {n : ℕ} (hn : 0 < n) : 0 < dd n := by
  unfold dd; exact Finset.card_pos.mpr ⟨1, by simp; omega⟩

private lemma summable_dd_shift (j : ℕ) : Summable (fun i : ℕ => (dd (j + i + 1) : ℝ) / 2 ^ (i + 1)) := by
  have h : Summable (fun i : ℕ => ((j + 1 : ℝ) + i) * (1/2) ^ i) := by
    have h1 := (summable_geometric_two).mul_left (j+1 : ℝ)
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2 : ℝ))
      (by norm_num [abs_of_pos])
    simpa [add_mul] using h1.add h2
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h
  have : (dd (j + i + 1) : ℝ) ≤ j + i + 1 := by exact_mod_cast Nat.card_divisors_le_self _
  rw [div_eq_mul_inv, pow_succ, mul_inv, one_div, inv_pow]
  have : (0:ℝ) ≤ (2 ^ i)⁻¹ := by positivity
  nlinarith

private lemma summable_dd : Summable (fun n : ℕ => (dd n : ℝ) / 2 ^ n) := by
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2 : ℝ))
    (by norm_num [abs_of_pos])
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h2
  have : (dd i : ℝ) ≤ i := by exact_mod_cast Nat.card_divisors_le_self _
  rw [div_eq_mul_inv, one_div, inv_pow, pow_one]
  have : (0:ℝ) ≤ (2 ^ i)⁻¹ := by positivity
  nlinarith

private lemma tail_pos {b : ℕ} (hb : 0 < b) (j : ℕ) : 0 < Tail b j := by
  unfold Tail
  apply mul_pos (by exact_mod_cast hb)
  apply (summable_dd_shift j).tsum_pos (fun i => by positivity) 0
  have := dd_pos (n := j + 0 + 1) (by omega)
  positivity

private lemma tail_upper (b j L : ℕ) :
    Tail b j ≤ b * ∑ i ∈ Finset.range L, (dd (j + i + 1) : ℝ) / 2 ^ (i + 1)
      + b * ((j + L + 2 : ℝ) / 2 ^ L) := by
  unfold Tail
  rw [← (summable_dd_shift j).sum_add_tsum_nat_add L, mul_add]
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
  refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff L).mpr (summable_dd_shift j))
    ((hg1.mul_left _).add (hg2.mul_left _))
  have : (dd (j + (i + L) + 1) : ℝ) ≤ j + L + 1 + i := by
    have := Nat.card_divisors_le_self (j + (i + L) + 1)
    have : (dd (j + (i + L) + 1) : ℝ) ≤ ((j + (i + L) + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  show (dd (j + (i + L) + 1) : ℝ) / 2 ^ (i + L + 1) ≤ _
  rw [show (2:ℝ) ^ (i + L + 1) = 2 ^ (L+1) * 2 ^ i by ring, one_div_pow]
  rw [div_le_iff₀ (by positivity)]
  field_simp
  linarith

private lemma tsum_pnat_of_zero (f : ℕ → ℝ) (h0 : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n : ℕ, f n := by
  apply Function.Injective.tsum_eq PNat.coe_injective
  intro n hn
  have : n ≠ 0 := by rintro rfl; exact hn h0
  exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩

/- The Lambert series identity `∑ 1/(2^n-1) = ∑ d(n)/2^n`. -/
private lemma series_eq : ∑' n : ℕ, (1 : ℝ) / (2 ^ n - 1) = ∑' n : ℕ, (dd n : ℝ) / 2 ^ n := by
  have h := tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) (r := 1/2) (by norm_num [abs_of_pos]) 0
  rw [← tsum_pnat_of_zero _ (by simp), ← tsum_pnat_of_zero _ (by simp [dd])]
  convert h using 1
  · apply tsum_congr; intro n
    have : (2:ℝ) ^ (n:ℕ) - 1 ≠ 0 := by
      have : (1:ℝ) < 2 ^ (n:ℕ) := one_lt_pow₀ (by norm_num) n.ne_zero
      linarith
    have h2 : (1 - (1/2:ℝ) ^ (n:ℕ)) ≠ 0 := by
      have : (1/2:ℝ) ^ (n:ℕ) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) n.ne_zero
      linarith
    rw [one_div_pow]
    field_simp
  · apply tsum_congr; intro n
    simp [ArithmeticFunction.sigma_zero_apply, dd, div_eq_mul_inv]

private lemma tail_eq_Zint {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : ∑' n : ℕ, (dd n : ℝ) / 2 ^ n = a / b) (j : ℕ) : Tail b j = Zint a b j := by
  have hsplit := summable_dd.sum_add_tsum_nat_add (j + 1)
  have htail : ∑' i : ℕ, (dd (i + (j + 1)) : ℝ) / 2 ^ (i + (j + 1)) =
      (1 / 2 ^ j) * ∑' i : ℕ, (dd (j + i + 1) : ℝ) / 2 ^ (i + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro i
    rw [show i + (j + 1) = j + i + 1 by ring,
      show (2:ℝ) ^ (j + i + 1) = 2 ^ j * 2 ^ (i + 1) by ring]
    field_simp
  rw [htail, h] at hsplit
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hT : Tail b j = 2 ^ j * (a - b * ∑ n ∈ Finset.range (j + 1), (dd n : ℝ) / 2 ^ n) := by
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

private lemma Zint_dvd (a : ℤ) (b k m : ℕ) (hd : ∀ n, k < n → n ≤ k + m → 2 ^ m ∣ dd n) :
    (2 : ℤ) ^ m ∣ Zint a b (k + m) := by
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

/- If `m` distinct primes each divide `n` exactly once, then `2^m ∣ d(n)`. -/
private lemma pow_two_dvd_dd {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ n ∧ ¬ p ^ 2 ∣ n) : 2 ^ S.card ∣ dd n := by
  unfold dd
  rw [Nat.card_divisors hn]
  have hsub : S ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨h1, h2, _⟩ := hS p hp
    exact Nat.mem_primeFactors.mpr ⟨h1, h2, hn⟩
  have : 2 ^ S.card = ∏ p ∈ S, (n.factorization p + 1) := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hS p hp
    have e1 : 1 ≤ n.factorization p := (h1.dvd_iff_one_le_factorization hn).mp h2
    have e2 : ¬ 2 ≤ n.factorization p := fun h => h3 ((h1.pow_dvd_iff_le_factorization hn).mpr h)
    omega
  rw [this]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

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

private lemma exists_param (b : ℕ) : ∃ m : ℕ, b ≤ m ∧ 1 ≤ m ∧ 15 * m ^ 5 < 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 5 (r := (2:ℝ)) (by norm_num)
  have h2 := (h.eventually (gt_mem_nhds (show (0:ℝ) < 1/15 by norm_num))).and
    (Filter.eventually_ge_atTop (max b 1))
  obtain ⟨m, hm, hmb⟩ := h2.exists
  refine ⟨m, le_of_max_le_left hmb, le_of_max_le_right hmb, ?_⟩
  have : (m : ℝ) ^ 5 < 1 / 15 * 2 ^ m := by
    rwa [div_lt_iff₀ (by positivity)] at hm
  have : (15 * m ^ 5 : ℝ) < 2 ^ m := by linarith
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
private lemma param_facts {b m : ℕ} (hbm : b ≤ m) (hm1 : 1 ≤ m) (hm : 15 * m ^ 5 < 2 ^ m) :
    let q := 2 * (m + m * m) * (m * m)
    m + 3 * q < 2 ^ m ∧ m + 3 * q ≤ 2 ^ q ∧ 8 * b ≤ 2 ^ q ∧
      2 * b * (3 + q) + 1 < 2 ^ m := by
  intro q
  have hq4 : q ≤ 4 * m ^ 4 := by
    have : m + m * m ≤ 2 * (m * m) := by nlinarith
    calc q ≤ 2 * (2 * (m * m)) * (m * m) := by simp only [q]; gcongr
      _ = 4 * m ^ 4 := by ring
  have hm5 : m ^ 4 ≤ m ^ 5 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hm5' : m ≤ m ^ 5 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 5 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hmq : m ≤ q := by
    simp only [q]; nlinarith
  have h2q : 2 ^ m ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hmq
  refine ⟨by omega, by omega, by omega, ?_⟩
  have : b * (3 + q) ≤ m * (3 + 4 * m ^ 4) := Nat.mul_le_mul hbm (by omega)
  have : m * (3 + 4 * m ^ 4) = 3 * m + 4 * m ^ 5 := by ring
  have : 2 * b * (3 + q) = 2 * (b * (3 + q)) := by ring
  omega

/- The averaging contradiction: the lower bounds `2^m ≤ Tail` along an arithmetic progression
are incompatible with the average size of the divisor function. -/
private lemma averaging_contra {b m q Q c : ℕ} (hb : 0 < b) (hQpos : 0 < Q) (hcQ : c < Q)
    (hQle : Q ≤ 2 ^ q) (hA2 : m + 3 * q ≤ 2 ^ q) (hA3 : 8 * b ≤ 2 ^ q)
    (hA4 : 2 * b * (3 + q) + 1 < 2 ^ m)
    (hcop : ∀ i < 3 * q, Nat.Coprime (c + m + i + 1) Q)
    (hlow : ∀ t, (2 : ℝ) ^ m ≤ Tail b (c + t * Q + m)) : False := by
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
  have hupt : ∀ t < X, Tail b (c + t * Q + m) ≤
      b * ∑ i ∈ Finset.range L, (dd (c + m + i + 1 + t * Q) : ℝ) / 2 ^ (i + 1)
        + b * ((2 * X ^ 2 : ℕ) / 2 ^ L : ℝ) := by
    intro t ht
    have h := tail_upper b (c + t * Q + m) L
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
  have hF : ∀ i ∈ Finset.range L, (∑ t ∈ Finset.range X, (dd (c + m + i + 1 + t * Q) : ℝ)) ≤ B := by
    intro i hi
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
      _ ≤ ∑ t ∈ Finset.range X, Tail b (c + t * Q + m) := Finset.sum_le_sum fun t _ => hlow t
      _ ≤ ∑ t ∈ Finset.range X, (b * ∑ i ∈ Finset.range L, (dd (c + m + i + 1 + t * Q) : ℝ) / 2 ^ (i + 1)
            + b * ((2 * X ^ 2 : ℕ) / 2 ^ L : ℝ)) :=
          Finset.sum_le_sum fun t ht => hupt t (by simpa using ht)
      _ = b * ∑ i ∈ Finset.range L, (∑ t ∈ Finset.range X, (dd (c + m + i + 1 + t * Q) : ℝ)) * (1 / 2) ^ (i + 1)
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

private theorem irrational_dd_series : Irrational (∑' n : ℕ, (dd n : ℝ) / 2 ^ n) := by
  rintro ⟨qr, hq⟩
  set a : ℤ := qr.num
  set b : ℕ := qr.den
  have hb : 0 < b := qr.pos
  have hx : ∑' n : ℕ, (dd n : ℝ) / 2 ^ n = a / b := by
    rw [← hq]; exact Rat.cast_def qr
  have hT : ∀ j, Tail b j = Zint a b j := tail_eq_Zint hb hx
  obtain ⟨m, hbm, hm1, hm⟩ := exists_param b
  obtain ⟨hA1, hA2, hA3, hA4⟩ := param_facts hbm hm1 hm
  set q := 2 * (m + m * m) * (m * m) with hqdef
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
  set Q : ℕ := ∏ ij ∈ S, pr ij ^ 2 with hQdef
  have hQpos : 0 < Q := Finset.prod_pos (fun ij _ => pow_pos (hprp ij).pos 2)
  have hQle : Q ≤ 2 ^ q := by
    calc Q ≤ ((2 ^ (m + m * m)) ^ 2) ^ S.card := by
          apply Finset.prod_le_pow_card
          intro ij hij
          exact Nat.pow_le_pow_left (hprhi ij hij) 2
      _ = 2 ^ q := by
          rw [hSdef, Finset.card_product, Finset.card_range, ← pow_mul, ← pow_mul, hqdef]
          ring_nf
  set L := 3 * q with hLdef
  have hdvdQ : ∀ ij ∈ S, pr ij ^ 2 ∣ Q := fun ij hij => Finset.dvd_prod_of_mem _ hij
  -- Chinese remainder theorem
  have hs : ∀ ij ∈ S, pr ij ^ 2 ≠ 0 := fun ij _ => (pow_pos (hprp ij).pos 2).ne'
  have pp : Set.Pairwise (S : Set (ℕ × ℕ)) (Function.onFun Nat.Coprime fun ij => pr ij ^ 2) := by
    intro x hx y hy hxy
    exact Nat.Coprime.pow 2 2 ((Nat.coprime_primes (hprp x) (hprp y)).2
      (fun h => hxy (hinj hx hy h)))
  set crt := Nat.chineseRemainderOfFinset (fun ij => pr ij ^ 2 + pr ij - (ij.1 + 1))
    (fun ij => pr ij ^ 2) S hs pp
  set c : ℕ := crt.1
  have hc : ∀ ij ∈ S, c ≡ pr ij ^ 2 + pr ij - (ij.1 + 1) [MOD pr ij ^ 2] := crt.2
  have hcQ : c < Q := Nat.chineseRemainderOfFinset_lt_prod _ _ hs pp
  -- the key congruence
  have hk : ∀ t, ∀ ij ∈ S, c + t * Q + (ij.1 + 1) ≡ pr ij [MOD pr ij ^ 2] := by
    intro t ij hij
    obtain ⟨R, hR⟩ := hdvdQ ij hij
    have hi : ij.1 < m := by
      simp only [hSdef, Finset.mem_product, Finset.mem_range] at hij; exact hij.1
    have hp := hprlo ij
    have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
    have e1 : c + t * Q ≡ c [MOD pr ij ^ 2] := by
      rw [hR, show t * (pr ij ^ 2 * R) = pr ij ^ 2 * (t * R) by ring]
      exact Nat.add_mul_mod_self_left _ _ _
    have e2 := (e1.trans (hc ij hij)).add_right (ij.1 + 1)
    rw [Nat.sub_add_cancel (by nlinarith)] at e2
    refine e2.trans ?_
    exact Nat.add_mod_left _ _
  -- forced divisibility
  have hforced : ∀ t, ∀ n, c + t * Q < n → n ≤ c + t * Q + m → 2 ^ m ∣ dd n := by
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
    apply pow_two_dvd_dd (by omega)
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    have hij : (i, j) ∈ S := by simp [hSdef, hi, (by simpa using hj : j < m)]
    have h := hk t (i, j) hij
    have hpp := hprp (i, j)
    refine ⟨hpp, (h.dvd_iff (Dvd.intro_left _ (pow_two _).symm)).2 dvd_rfl, ?_⟩
    rw [h.dvd_iff dvd_rfl]
    intro hd
    have := Nat.le_of_dvd hpp.pos hd
    have := hpp.two_le
    nlinarith
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
      ((hk 0 ij hij).dvd_iff (Dvd.intro_left _ (pow_two _).symm)).2 dvd_rfl
    have h2 : c + m + i + 1 = (c + 0 * Q + (ij.1 + 1)) + (m + i - ij.1) := by omega
    rw [h2] at hd
    have h3 := (Nat.dvd_add_right h1).mp hd
    have h4 := Nat.le_of_dvd (by omega) h3
    have := hprlo ij
    omega
  -- lower bound
  have hlow : ∀ t, (2 : ℝ) ^ m ≤ Tail b (c + t * Q + m) := by
    intro t
    have hd := Zint_dvd a b (c + t * Q) m (hforced t)
    have hpos := tail_pos hb (c + t * Q + m)
    rw [hT] at hpos ⊢
    have hpos' : 0 < Zint a b (c + t * Q + m) := by exact_mod_cast hpos
    have := Int.le_of_dvd hpos' hd
    exact_mod_cast this
  exact averaging_contra hb hQpos hcQ hQle hA2 hA3 hA4 hcop hlow

/-- Erdős 257 for `A = ℕ`: the Erdős–Borwein constant `∑_{n ≥ 1} 1/(2^n - 1) = ∑_{n ≥ 1} d(n)/2^n`
is irrational. Known: P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math.
Soc. (N.S.) 12 (1948), 63–66, Theorem (`f(1/t)` irrational for every integer `|t| > 1`; here
`t = 2`). The `n = 0` term is `1/0 = 0` in Lean, so the sum is the sum over `n ≥ 1`. -/
theorem Opn.erdos_257_all_naturals :
    Irrational (∑' n : ℕ, (1 : ℝ) / (2 ^ n - 1)) := by
  rw [series_eq]
  exact irrational_dd_series
