import Mathlib
import Nodes.«variant-d08712d9».Context

private def SS (n : ℕ) : Prop := ∃ a b : ℕ, n = a ^ 2 + b ^ 2

private lemma SS_iff (n : ℕ) : SS n ↔ ∀ {q : ℕ}, q.Prime → q % 4 = 3 → Even (padicValNat q n) := by
  unfold SS
  constructor
  · intro h q hq h3
    by_cases hqn : q ∈ n.primeFactors
    · exact Nat.eq_sq_add_sq_iff.mp h q hqn h3
    · have : padicValNat q n = 0 := by
        by_cases hn : n = 0
        · subst hn; simp
        · apply padicValNat.eq_zero_of_not_dvd
          intro hd
          exact hqn (Nat.mem_primeFactors.mpr ⟨hq, hd, hn⟩)
      rw [this]; exact ⟨0, rfl⟩
  · intro h
    apply Nat.eq_sq_add_sq_iff.mpr
    intro q hq h3
    exact h (Nat.prime_of_mem_primeFactors hq) h3

private lemma pv_split {q m n : ℕ} (hq : q.Prime) (h : Nat.Coprime m n) :
    padicValNat q m = 0 ∨ padicValNat q n = 0 := by
  by_cases hm : q ∣ m
  · right
    apply padicValNat.eq_zero_of_not_dvd
    intro hn
    have h1 : q ∣ Nat.gcd m n := Nat.dvd_gcd hm hn
    rw [h.gcd_eq_one] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
  · left; exact padicValNat.eq_zero_of_not_dvd hm

private lemma SS_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    SS (m * n) ↔ SS m ∧ SS n := by
  rw [SS_iff, SS_iff, SS_iff]
  constructor
  · intro H
    constructor
    · intro q hq h3
      haveI := Fact.mk hq
      have := H hq h3
      rw [padicValNat.mul hm hn] at this
      rcases pv_split hq h with h0 | h0
      · rw [h0]; exact ⟨0, rfl⟩
      · rwa [h0, add_zero] at this
    · intro q hq h3
      haveI := Fact.mk hq
      have := H hq h3
      rw [padicValNat.mul hm hn] at this
      rcases pv_split hq h with h0 | h0
      · rwa [h0, zero_add] at this
      · rw [h0]; exact ⟨0, rfl⟩
  · rintro ⟨H1, H2⟩ q hq h3
    haveI := Fact.mk hq
    rw [padicValNat.mul hm hn]
    exact (H1 hq h3).add (H2 hq h3)

private noncomputable def chi : ArithmeticFunction ℕ :=
  ⟨fun n => by classical exact if n ≠ 0 ∧ SS n then 1 else 0, by simp⟩

private lemma chi_apply (n : ℕ) : chi n = by classical exact if n ≠ 0 ∧ SS n then 1 else 0 := rfl

private lemma chi_mult : chi.IsMultiplicative := by
  classical
  refine ⟨?_, ?_⟩
  · rw [chi_apply]; simp only [ne_eq, one_ne_zero, not_false_eq_true, true_and]
    rw [if_pos ⟨1, 0, by norm_num⟩]
  · intro m n h
    rw [chi_apply, chi_apply, chi_apply]
    by_cases hm : m = 0
    · subst hm; simp
    by_cases hn : n = 0
    · subst hn; simp
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    rw [SS_mul hm hn h]
    by_cases h1 : SS m <;> by_cases h2 : SS n <;> simp [hm, hn, h1, h2]

private noncomputable def ff (n : ℕ) : ℕ := (chi * ArithmeticFunction.zeta) n

private lemma ff_eq (n : ℕ) : ff n = ∑ d ∈ n.divisors, chi d := by
  unfold ff; rw [← ArithmeticFunction.natCoe_nat ArithmeticFunction.zeta, ArithmeticFunction.coe_mul_zeta_apply]

private def ex (p : ℕ) : ℕ := if p % 4 = 3 then 2 else 1

private lemma ff_prime_pow {p : ℕ} (hp : p.Prime) : ff (p ^ ex p) = 2 := by
  classical
  haveI := Fact.mk hp
  rw [ff_eq, Nat.sum_divisors_prime_pow hp]
  have c0 : chi 1 = 1 := chi_mult.map_one
  unfold ex
  split_ifs with h3
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, c0, zero_add]
    have c1 : chi p = 0 := by
      rw [chi_apply, if_neg]
      rintro ⟨_, hs⟩
      have := (SS_iff p).mp hs hp h3
      rw [padicValNat_self] at this
      exact Nat.not_even_one this
    have c2 : chi (p ^ 2) = 1 := by
      rw [chi_apply, if_pos ⟨pow_ne_zero 2 hp.ne_zero, p, 0, by ring⟩]
    rw [c1, c2]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, c0, zero_add]
    have c1 : chi p = 1 := by
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq h3
      rw [chi_apply, if_pos ⟨hp.ne_zero, a, b, hab.symm⟩]
    rw [c1]

private lemma ff_mult : (chi * ArithmeticFunction.zeta).IsMultiplicative :=
  chi_mult.mul ArithmeticFunction.isMultiplicative_zeta

private lemma pow_two_dvd_ff {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ^ ex p ∣ n ∧ ¬ p ^ (ex p + 1) ∣ n) : 2 ^ S.card ∣ ff n := by
  unfold ff
  rw [ff_mult.multiplicative_factorization (chi * ArithmeticFunction.zeta) hn]
  have hsub : S ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨h1, h2, _⟩ := hS p hp
    have hex : 1 ≤ ex p := by unfold ex; split_ifs <;> norm_num
    exact Nat.mem_primeFactors.mpr ⟨h1, (dvd_pow_self p (by omega)).trans h2, hn⟩
  have : 2 ^ S.card = ∏ p ∈ S, (chi * ArithmeticFunction.zeta) (p ^ n.factorization p) := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hS p hp
    have e1 : ex p ≤ n.factorization p := (h1.pow_dvd_iff_le_factorization hn).mp h2
    have e2 : ¬ ex p + 1 ≤ n.factorization p :=
      fun h => h3 ((h1.pow_dvd_iff_le_factorization hn).mpr h)
    rw [show n.factorization p = ex p by omega]
    exact (ff_prime_pow h1).symm
  rw [this, Finsupp.prod, Nat.support_factorization]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

private def dd (n : ℕ) : ℕ := n.divisors.card

private lemma chi_le_one (n : ℕ) : chi n ≤ 1 := by
  classical
  rw [chi_apply]; split_ifs <;> norm_num

private lemma fk_le_dd (k n : ℕ) : ff n ≤ dd n := by
  rw [ff_eq, dd, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun d _ => chi_le_one d)

private lemma fk_le (k n : ℕ) : ff n ≤ n := (fk_le_dd k n).trans (Nat.card_divisors_le_self n)

private lemma fk_pos (k : ℕ) {n : ℕ} (hn : 0 < n) : 0 < ff n := by
  rw [ff_eq]
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩
  have : chi 1 ≤ ∑ d ∈ n.divisors, chi d := Finset.single_le_sum (fun d _ => Nat.zero_le _) h1
  rw [chi_mult.map_one] at this
  omega

private lemma ff_real (N : ℕ) :
    (ff N : ℝ) = ∑ a ∈ N.divisors, (if ∃ x y : ℕ, a = x ^ 2 + y ^ 2 then (1 : ℝ) else 0) := by
  classical
  rw [ff_eq]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [chi_apply]
  by_cases h : ∃ x y : ℕ, a = x ^ 2 + y ^ 2
  · rw [if_pos ⟨ha0, h⟩, if_pos h]; norm_num
  · rw [if_neg (fun hh => h hh.2), if_neg h]; norm_num

private lemma ex_pos (p : ℕ) : 0 < ex p := by unfold ex; split_ifs <;> norm_num

private lemma ex_le (p : ℕ) : ex p + 1 ≤ 2 + 1 := by unfold ex; split_ifs <;> norm_num

private lemma tsum_pnat_of_zero (f : ℕ → ℝ) (h0 : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n : ℕ, f n := by
  apply Function.Injective.tsum_eq PNat.coe_injective
  intro n hn
  have : n ≠ 0 := by rintro rfl; exact hn h0
  exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩

/- The Lambert series identity `∑_{n squarefree} 1/(2^n-1) = ∑ f(n)/2^n`. -/
private lemma series_eq :
    ∑' n : {n : ℕ | ∃ a b : ℕ, n = a ^ 2 + b ^ 2}, (1 : ℝ) / (2 ^ n.1 - 1) = ∑' n : ℕ, (ff n : ℝ) / 2 ^ n := by
  classical
  set s : ℕ → ℝ := fun n => if ∃ a b : ℕ, n = a ^ 2 + b ^ 2 then 1 else 0 with hs
  have hs01 : ∀ n, 0 ≤ s n ∧ s n ≤ 1 := fun n => by simp only [hs]; split_ifs <;> norm_num
  set F : ℕ+ × ℕ+ → ℝ := fun p => s p.1 * (1/2 : ℝ) ^ ((p.1 : ℕ) * p.2) with hF
  have hFsum : Summable F := by
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (hs01 _).1 (by positivity)) (fun p => ?_)
      (summable_prod_mul_pow (𝕜 := ℝ) 0 (r := 1/2) (by norm_num [abs_of_pos]))
    simp only [hF, pow_zero, one_mul]
    exact mul_le_of_le_one_left (by positivity) (hs01 _).2
  -- Step A
  have hA : ∑' n : {n : ℕ | ∃ a b : ℕ, n = a ^ 2 + b ^ 2}, (1 : ℝ) / (2 ^ n.1 - 1)
      = ∑' n : ℕ, s n * (1 / (2 ^ n - 1)) := by
    rw [tsum_subtype {n : ℕ | ∃ a b : ℕ, n = a ^ 2 + b ^ 2} (fun n => (1 : ℝ) / (2 ^ n - 1))]
    apply tsum_congr; intro n
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hs]
    split_ifs <;> simp
  -- Step C
  have hC : ∀ n : ℕ+, s n * (1 / (2 ^ (n : ℕ) - 1)) = ∑' k : ℕ+, F (n, k) := by
    intro n
    have hy : (1/2 : ℝ) ^ (n : ℕ) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) n.ne_zero
    simp only [hF]
    rw [tsum_mul_left, tsum_pnat_eq_tsum_succ (f := fun k => (1/2 : ℝ) ^ ((n : ℕ) * k))]
    simp only [pow_mul, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity) hy]
    congr 1
    have : (2:ℝ) ^ (n:ℕ) - 1 ≠ 0 := by
      have : (1:ℝ) < 2 ^ (n:ℕ) := one_lt_pow₀ (by norm_num) n.ne_zero
      linarith
    have h2 : (1 - (1/2:ℝ) ^ (n:ℕ)) ≠ 0 := by linarith
    rw [one_div_pow]
    field_simp
  have hFe : Summable (F ∘ _root_.sigmaAntidiagonalEquivProd) :=
    (_root_.sigmaAntidiagonalEquivProd.summable_iff).2 hFsum
  have hinner : ∀ N : ℕ+, ∑' x : (N : ℕ).divisorsAntidiagonal,
      (F ∘ _root_.sigmaAntidiagonalEquivProd) ⟨N, x⟩ = (ff N : ℝ) / 2 ^ (N : ℕ) := by
    intro N
    rw [tsum_fintype, Finset.univ_eq_attach]
    simp only [Function.comp_apply, _root_.sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors,
      Equiv.coe_fn_mk, PNat.mk_coe, hF]
    rw [Finset.sum_attach (N : ℕ).divisorsAntidiagonal
      (fun x : ℕ × ℕ => s x.1 * (1/2 : ℝ) ^ (x.1 * x.2))]
    rw [Finset.sum_congr rfl (g := fun x : ℕ × ℕ => s x.1 * (1/2 : ℝ) ^ (N : ℕ))
      (fun x hx => by rw [(Nat.mem_divisorsAntidiagonal.mp hx).1])]
    rw [Nat.sum_divisorsAntidiagonal (fun a _ => s a * (1/2 : ℝ) ^ (N : ℕ)), ← Finset.sum_mul]
    rw [← ff_real, one_div_pow, mul_one_div]
  calc ∑' n : {n : ℕ | ∃ a b : ℕ, n = a ^ 2 + b ^ 2}, (1 : ℝ) / (2 ^ n.1 - 1)
      = ∑' n : ℕ, s n * (1 / (2 ^ n - 1)) := hA
    _ = ∑' n : ℕ+, s n * (1 / (2 ^ (n : ℕ) - 1)) := (tsum_pnat_of_zero _ (by norm_num)).symm
    _ = ∑' n : ℕ+, ∑' k : ℕ+, F (n, k) := tsum_congr hC
    _ = ∑' p : ℕ+ × ℕ+, F p := hFsum.tsum_prod.symm
    _ = ∑' x, (F ∘ _root_.sigmaAntidiagonalEquivProd) x := (_root_.sigmaAntidiagonalEquivProd.tsum_eq F).symm
    _ = ∑' N : ℕ+, ∑' x : (N : ℕ).divisorsAntidiagonal,
          (F ∘ _root_.sigmaAntidiagonalEquivProd) ⟨N, x⟩ := hFe.tsum_sigma
    _ = ∑' N : ℕ+, (ff N : ℝ) / 2 ^ (N : ℕ) := tsum_congr hinner
    _ = ∑' n : ℕ, (ff n : ℝ) / 2 ^ n := tsum_pnat_of_zero (fun n => (ff n : ℝ) / 2 ^ n) (by simp [ff_eq])

/- `b` times the "tail" `∑_{i ≥ 1} f_k(j+i) / 2^i`. -/
private noncomputable def Tail (k b : ℕ) (j : ℕ) : ℝ := b * ∑' i : ℕ, (ff (j + i + 1) : ℝ) / 2 ^ (i + 1)

/- The integer that the tail equals when the series is `a / b`. -/
private noncomputable def Zint (k : ℕ) (a : ℤ) (b : ℕ) (j : ℕ) : ℤ :=
  a * 2 ^ j - b * ∑ n ∈ Finset.range (j + 1), (ff n : ℤ) * 2 ^ (j - n)


private lemma summable_fk_shift (k : ℕ) (j : ℕ) : Summable (fun i : ℕ => (ff (j + i + 1) : ℝ) / 2 ^ (i + 1)) := by
  have h : Summable (fun i : ℕ => ((j + 1 : ℝ) + i) * (1/2) ^ i) := by
    have h1 := (summable_geometric_two).mul_left (j+1 : ℝ)
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2 : ℝ))
      (by norm_num [abs_of_pos])
    simpa [add_mul] using h1.add h2
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h
  have : (ff (j + i + 1) : ℝ) ≤ j + i + 1 := by exact_mod_cast fk_le k _
  rw [div_eq_mul_inv, pow_succ, mul_inv, one_div, inv_pow]
  have : (0:ℝ) ≤ (2 ^ i)⁻¹ := by positivity
  nlinarith

private lemma summable_fk (k : ℕ) : Summable (fun n : ℕ => (ff n : ℝ) / 2 ^ n) := by
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2 : ℝ))
    (by norm_num [abs_of_pos])
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h2
  have : (ff i : ℝ) ≤ i := by exact_mod_cast fk_le k _
  rw [div_eq_mul_inv, one_div, inv_pow, pow_one]
  have : (0:ℝ) ≤ (2 ^ i)⁻¹ := by positivity
  nlinarith

private lemma tail_pos (k : ℕ) {b : ℕ} (hb : 0 < b) (j : ℕ) : 0 < Tail k b j := by
  unfold Tail
  apply mul_pos (by exact_mod_cast hb)
  apply (summable_fk_shift k j).tsum_pos (fun i => by positivity) 0
  have := fk_pos k (n := j + 0 + 1) (by omega)
  positivity

private lemma tail_upper (k : ℕ) (b j L : ℕ) :
    Tail k b j ≤ b * ∑ i ∈ Finset.range L, (ff (j + i + 1) : ℝ) / 2 ^ (i + 1)
      + b * ((j + L + 2 : ℝ) / 2 ^ L) := by
  unfold Tail
  rw [← (summable_fk_shift k j).sum_add_tsum_nat_add L, mul_add]
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
  refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff L).mpr (summable_fk_shift k j))
    ((hg1.mul_left _).add (hg2.mul_left _))
  have : (ff (j + (i + L) + 1) : ℝ) ≤ j + L + 1 + i := by
    have := fk_le k (j + (i + L) + 1)
    have : (ff (j + (i + L) + 1) : ℝ) ≤ ((j + (i + L) + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  show (ff (j + (i + L) + 1) : ℝ) / 2 ^ (i + L + 1) ≤ _
  rw [show (2:ℝ) ^ (i + L + 1) = 2 ^ (L+1) * 2 ^ i by ring, one_div_pow]
  rw [div_le_iff₀ (by positivity)]
  field_simp
  linarith

private lemma tail_eq_Zint (k : ℕ) {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : ∑' n : ℕ, (ff n : ℝ) / 2 ^ n = a / b) (j : ℕ) : Tail k b j = Zint k a b j := by
  have hsplit := (summable_fk k).sum_add_tsum_nat_add (j + 1)
  have htail : ∑' i : ℕ, (ff (i + (j + 1)) : ℝ) / 2 ^ (i + (j + 1)) =
      (1 / 2 ^ j) * ∑' i : ℕ, (ff (j + i + 1) : ℝ) / 2 ^ (i + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro i
    rw [show i + (j + 1) = j + i + 1 by ring,
      show (2:ℝ) ^ (j + i + 1) = 2 ^ j * 2 ^ (i + 1) by ring]
    field_simp
  rw [htail, h] at hsplit
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hT : Tail k b j = 2 ^ j * (a - b * ∑ n ∈ Finset.range (j + 1), (ff n : ℝ) / 2 ^ n) := by
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

private lemma Zint_dvd (k : ℕ) (a : ℤ) (b s m : ℕ) (hd : ∀ n, s < n → n ≤ s + m → 2 ^ m ∣ ff n) :
    (2 : ℤ) ^ m ∣ Zint k a b (s + m) := by
  unfold Zint
  apply dvd_sub
  · exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  · apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro n hn
    have hn' : n ≤ s + m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    by_cases hnk : n ≤ s
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

private lemma sum_fk_AP_le (k r Q X : ℕ) (hcop : Nat.Coprime r Q)
    (hX : ∀ t < X, r + t * Q ≤ X * X) :
    (∑ t ∈ Finset.range X, (ff (r + t * Q) : ℝ)) ≤ 2 * X * (2 + Real.log X) := by
  refine le_trans ?_ (sum_dd_AP_le r Q X hcop hX)
  exact Finset.sum_le_sum fun t _ => by exact_mod_cast fk_le_dd k _

/- The averaging contradiction: the lower bounds `2^m ≤ Tail` along an arithmetic progression
are incompatible with the average size of the divisor function. -/
private lemma averaging_contra {k b m q Q c : ℕ} (hb : 0 < b) (hQpos : 0 < Q) (hcQ : c < Q)
    (hQle : Q ≤ 2 ^ q) (hA2 : m + 3 * q ≤ 2 ^ q) (hA3 : 8 * b ≤ 2 ^ q)
    (hA4 : 2 * b * (3 + q) + 1 < 2 ^ m)
    (hcop : ∀ i < 3 * q, Nat.Coprime (c + m + i + 1) Q)
    (hlow : ∀ t, (2 : ℝ) ^ m ≤ Tail k b (c + t * Q + m)) : False := by
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
  have hupt : ∀ t < X, Tail k b (c + t * Q + m) ≤
      b * ∑ i ∈ Finset.range L, (ff (c + m + i + 1 + t * Q) : ℝ) / 2 ^ (i + 1)
        + b * ((2 * X ^ 2 : ℕ) / 2 ^ L : ℝ) := by
    intro t ht
    have h := tail_upper k b (c + t * Q + m) L
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
  have hF : ∀ i ∈ Finset.range L, (∑ t ∈ Finset.range X, (ff (c + m + i + 1 + t * Q) : ℝ)) ≤ B := by
    intro i hi
    apply sum_fk_AP_le k _ _ _ (hcop i (by simpa using hi))
    intro t ht
    have := hrange t ht
    have : i < L := by simpa using hi
    omega
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX1)
    positivity
  have hmain : (X : ℝ) * 2 ^ m ≤ b * B + X := by
    calc (X : ℝ) * 2 ^ m = ∑ t ∈ Finset.range X, (2 : ℝ) ^ m := by simp
      _ ≤ ∑ t ∈ Finset.range X, Tail k b (c + t * Q + m) := Finset.sum_le_sum fun t _ => hlow t
      _ ≤ ∑ t ∈ Finset.range X, (b * ∑ i ∈ Finset.range L, (ff (c + m + i + 1 + t * Q) : ℝ) / 2 ^ (i + 1)
            + b * ((2 * X ^ 2 : ℕ) / 2 ^ L : ℝ)) :=
          Finset.sum_le_sum fun t ht => hupt t (by simpa using ht)
      _ = b * ∑ i ∈ Finset.range L, (∑ t ∈ Finset.range X, (ff (c + m + i + 1 + t * Q) : ℝ)) * (1 / 2) ^ (i + 1)
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


private lemma exists_param (b k : ℕ) : ∃ m : ℕ, b ≤ m ∧ k ≤ m ∧ 1 ≤ m ∧ 15 * m ^ 6 < 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 6 (r := (2:ℝ)) (by norm_num)
  have h2 := (h.eventually (gt_mem_nhds (show (0:ℝ) < 1/15 by norm_num))).and
    (Filter.eventually_ge_atTop (max (max b k) 1))
  obtain ⟨m, hm, hmb⟩ := h2.exists
  refine ⟨m, le_of_max_le_left (le_of_max_le_left hmb), le_of_max_le_right (le_of_max_le_left hmb),
    le_of_max_le_right hmb, ?_⟩
  have : (m : ℝ) ^ 6 < 1 / 15 * 2 ^ m := by
    rwa [div_lt_iff₀ (by positivity)] at hm
  have : (15 * m ^ 6 : ℝ) < 2 ^ m := by linarith
  exact_mod_cast this

/- Numerical facts about the parameters. -/
private lemma param_facts {b k m : ℕ} (hbm : b ≤ m) (hkm : k ≤ m) (hm1 : 1 ≤ m)
    (hm : 15 * m ^ 6 < 2 ^ m) :
    let q := (k + 1) * (m + m * m) * (m * m)
    m + 3 * q < 2 ^ m ∧ m + 3 * q ≤ 2 ^ q ∧ 8 * b ≤ 2 ^ q ∧ 2 * b * (3 + q) + 1 < 2 ^ m := by
  intro q
  have hq5 : q ≤ 4 * m ^ 5 := by
    have : m + m * m ≤ 2 * (m * m) := by nlinarith
    calc q ≤ (2 * m) * (2 * (m * m)) * (m * m) := by simp only [q]; gcongr; omega
      _ = 4 * m ^ 5 := by ring
  have hm56 : m ^ 5 ≤ m ^ 6 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hm6 : m ≤ m ^ 6 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 6 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hmq : m ≤ q := by
    simp only [q]
    have : 1 ≤ (k + 1) * (m + m * m) := by nlinarith
    nlinarith
  have h2q : 2 ^ m ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hmq
  refine ⟨by omega, by omega, by omega, ?_⟩
  have : b * (3 + q) ≤ m * (3 + 4 * m ^ 5) := Nat.mul_le_mul hbm (by omega)
  have : m * (3 + 4 * m ^ 5) = 3 * m + 4 * m ^ 6 := by ring
  have : 2 * b * (3 + q) = 2 * (b * (3 + q)) := by ring
  omega

private theorem irrational_ff_series :
    Irrational (∑' n : ℕ, (ff n : ℝ) / 2 ^ n) := by
  set k : ℕ := 2 with hkdef
  rintro ⟨qr, hq⟩
  set a : ℤ := qr.num
  set b : ℕ := qr.den
  have hb : 0 < b := qr.pos
  have hx : ∑' n : ℕ, (ff n : ℝ) / 2 ^ n = a / b := by
    rw [← hq]; exact Rat.cast_def qr
  have hT : ∀ j, Tail k b j = Zint k a b j := tail_eq_Zint k hb hx
  obtain ⟨m, hbm, hkm, hm1, hm⟩ := exists_param b k
  obtain ⟨hA1, hA2, hA3, hA4⟩ := param_facts hbm hkm hm1 hm
  set q := (k + 1) * (m + m * m) * (m * m) with hqdef
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
  set Q : ℕ := ∏ ij ∈ S, pr ij ^ (ex (pr ij) + 1) with hQdef
  have hQpos : 0 < Q := Finset.prod_pos (fun ij _ => pow_pos (hprp ij).pos _)
  have hQle : Q ≤ 2 ^ q := by
    calc Q ≤ ((2 ^ (m + m * m)) ^ (k + 1)) ^ S.card := by
          apply Finset.prod_le_pow_card
          intro ij hij
          exact (Nat.pow_le_pow_right (hprp ij).pos (ex_le _)).trans (Nat.pow_le_pow_left (hprhi ij hij) (k + 1))
      _ = 2 ^ q := by
          rw [hSdef, Finset.card_product, Finset.card_range, ← pow_mul, ← pow_mul, hqdef]
          ring_nf
  set L := 3 * q with hLdef
  have hdvdQ : ∀ ij ∈ S, pr ij ^ (ex (pr ij) + 1) ∣ Q := fun ij hij => Finset.dvd_prod_of_mem _ hij
  -- Chinese remainder theorem
  have hs : ∀ ij ∈ S, pr ij ^ (ex (pr ij) + 1) ≠ 0 := fun ij _ => (pow_pos (hprp ij).pos _).ne'
  have pp : Set.Pairwise (S : Set (ℕ × ℕ))
      (Function.onFun Nat.Coprime fun ij => pr ij ^ (ex (pr ij) + 1)) := by
    intro x hx y hy hxy
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprp x) (hprp y)).2
      (fun h => hxy (hinj hx hy h)))
  set crt := Nat.chineseRemainderOfFinset (fun ij => pr ij ^ (ex (pr ij) + 1) + pr ij ^ ex (pr ij) - (ij.1 + 1))
    (fun ij => pr ij ^ (ex (pr ij) + 1)) S hs pp
  set c : ℕ := crt.1
  have hc : ∀ ij ∈ S, c ≡ pr ij ^ (ex (pr ij) + 1) + pr ij ^ ex (pr ij) - (ij.1 + 1) [MOD pr ij ^ (ex (pr ij) + 1)] := crt.2
  have hcQ : c < Q := Nat.chineseRemainderOfFinset_lt_prod _ _ hs pp
  -- the key congruence
  have hcong : ∀ t, ∀ ij ∈ S, c + t * Q + (ij.1 + 1) ≡ pr ij ^ ex (pr ij) [MOD pr ij ^ (ex (pr ij) + 1)] := by
    intro t ij hij
    obtain ⟨R, hR⟩ := hdvdQ ij hij
    have hi : ij.1 < m := by
      simp only [hSdef, Finset.mem_product, Finset.mem_range] at hij; exact hij.1
    have hp := hprlo ij
    have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
    have hpk : pr ij ≤ pr ij ^ ex (pr ij) := Nat.le_self_pow (ex_pos _).ne' _
    have e1 : c + t * Q ≡ c [MOD pr ij ^ (ex (pr ij) + 1)] := by
      rw [hR, show t * (pr ij ^ (ex (pr ij) + 1) * R) = pr ij ^ (ex (pr ij) + 1) * (t * R) by ring]
      exact Nat.add_mul_mod_self_left _ _ _
    have e2 := (e1.trans (hc ij hij)).add_right (ij.1 + 1)
    rw [Nat.sub_add_cancel (by omega)] at e2
    refine e2.trans ?_
    exact Nat.add_mod_left _ _
  -- forced divisibility
  have hforced : ∀ t, ∀ n, c + t * Q < n → n ≤ c + t * Q + m → 2 ^ m ∣ ff n := by
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
    apply pow_two_dvd_ff (by omega)
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    have hij : (i, j) ∈ S := by simp [hSdef, hi, (by simpa using hj : j < m)]
    have h := hcong t (i, j) hij
    have hpp := hprp (i, j)
    refine ⟨hpp, (h.dvd_iff (pow_dvd_pow _ (Nat.le_succ _))).2 dvd_rfl, ?_⟩
    rw [h.dvd_iff dvd_rfl]
    intro hd
    have := (Nat.pow_dvd_pow_iff_le_right hpp.one_lt).mp hd
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
      ((hcong 0 ij hij).dvd_iff ((dvd_pow_self _ (ex_pos _).ne').trans (pow_dvd_pow _ (Nat.le_succ _)))).2
        (dvd_pow_self _ (ex_pos _).ne')
    have h2 : c + m + i + 1 = (c + 0 * Q + (ij.1 + 1)) + (m + i - ij.1) := by omega
    rw [h2] at hd
    have h3 := (Nat.dvd_add_right h1).mp hd
    have h4 := Nat.le_of_dvd (by omega) h3
    have := hprlo ij
    have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  -- lower bound
  have hlow : ∀ t, (2 : ℝ) ^ m ≤ Tail k b (c + t * Q + m) := by
    intro t
    have hd := Zint_dvd k a b (c + t * Q) m (hforced t)
    have hpos := tail_pos k hb (c + t * Q + m)
    rw [hT] at hpos ⊢
    have hpos' : 0 < Zint k a b (c + t * Q + m) := by exact_mod_cast hpos
    have := Int.le_of_dvd hpos' hd
    exact_mod_cast this
  exact averaging_contra hb hQpos hcQ hQle hA2 hA3 hA4 hcop hlow

/-- Erdős 257 for `A` the sums of two squares `{a² + b²}`. Known: D. Duverney and Y. Tachiya,
*Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*,
Forum Math. 31 (2019), 1557–1566, Example 1.2 (a case of Corollary 1.2 with `s = ∞` and `E`
the prime `2`, the primes `≡ 1 (mod 4)` and the squares of the primes `≡ 3 (mod 4)`): `1` and
`∑_{n ≥ 1} 1/(q^(j s_n^i) - 1)` are linearly independent over `ℚ` for every integer `|q| > 1`,
where `s_n` runs over the positive sums of two squares; take `q = 2`, `i = j = 1`. The element
`0 = 0² + 0²` contributes `1/0 = 0` in Lean. -/
theorem Opn.erdos_257_sums_of_two_squares :
    Irrational (∑' m : {m : ℕ | ∃ a b, m = a ^ 2 + b ^ 2}, (1 : ℝ) / (2 ^ m.1 - 1)) := by
  rw [series_eq]
  exact irrational_ff_series
