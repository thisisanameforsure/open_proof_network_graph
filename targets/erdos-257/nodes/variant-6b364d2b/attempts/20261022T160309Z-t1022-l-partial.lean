import Mathlib
import Nodes.«variant-6b364d2b».Context

/-- the summand on pairs `(m, a)`: `(1/2)^m` when `a ∈ A`, `a ∣ m`, `m ≠ 0`. -/
private noncomputable def lamG (A : Set ℕ) [DecidablePred (· ∈ A)] (p : ℕ × ℕ) : ℝ :=
  if p.2 ∈ A ∧ p.2 ∣ p.1 ∧ p.1 ≠ 0 then (1 / 2 : ℝ) ^ p.1 else 0

private lemma lamG_nonneg (A : Set ℕ) [DecidablePred (· ∈ A)] (p : ℕ × ℕ) : 0 ≤ lamG A p := by
  unfold lamG; split_ifs <;> positivity

private lemma lamG_row (A : Set ℕ) [DecidablePred (· ∈ A)] (m : ℕ) :
    ∑' a, lamG A (m, a) = (((Nat.divisors m).filter (· ∈ A)).card : ℝ) * (1 / 2 : ℝ) ^ m := by
  rw [tsum_eq_sum (s := (Nat.divisors m).filter (· ∈ A))]
  · rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at ha
    simp [lamG, ha.1.1, ha.1.2, ha.2]
  · intro a ha
    simp only [Finset.mem_filter, Nat.mem_divisors, not_and] at ha
    unfold lamG
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact ha ⟨h2, h3⟩ h1

private lemma lamG_row_summable (A : Set ℕ) [DecidablePred (· ∈ A)] (m : ℕ) : Summable fun a => lamG A (m, a) := by
  apply summable_of_ne_finset_zero (s := (Nat.divisors m).filter (· ∈ A))
  intro a ha
  simp only [Finset.mem_filter, Nat.mem_divisors, not_and] at ha
  unfold lamG
  rw [if_neg]
  rintro ⟨h1, h2, h3⟩
  exact ha ⟨h2, h3⟩ h1

private lemma lamG_summable (A : Set ℕ) [DecidablePred (· ∈ A)] : Summable (lamG A) := by
  rw [summable_prod_of_nonneg (lamG_nonneg A)]
  refine ⟨lamG_row_summable A, ?_⟩
  simp_rw [lamG_row]
  have hg : Summable fun m : ℕ => ((m : ℝ) ^ 1) * (1 / 2 : ℝ) ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hg
  gcongr
  rw [pow_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self m)

private lemma lamG_col (A : Set ℕ) [DecidablePred (· ∈ A)] (a : ℕ) :
    ∑' m, lamG A (m, a) = if a ∈ A then (1 : ℝ) / (2 ^ a - 1) else 0 := by
  by_cases ha : a ∈ A
  swap
  · simp [lamG, ha]
  rw [if_pos ha]
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0; simp [lamG]
  have hinj : Function.Injective fun k : ℕ => a * (k + 1) := by
    intro x y h; simp only at h
    have := Nat.eq_of_mul_eq_mul_left hpos h; omega
  have hsupp : Function.support (fun m => lamG A (m, a)) ⊆ Set.range fun k : ℕ => a * (k + 1) := by
    intro m hm
    simp only [Function.mem_support, lamG, ne_eq, ite_eq_right_iff, Classical.not_imp] at hm
    obtain ⟨⟨_, ⟨c, hc⟩, hm0⟩, _⟩ := hm
    refine ⟨c - 1, ?_⟩
    have : c ≠ 0 := by rintro rfl; simp at hc; exact hm0 hc
    simp only; rw [hc]; congr 1; omega
  rw [← hinj.tsum_eq hsupp]
  have hterm : ∀ k : ℕ, lamG A (a * (k + 1), a) = (1 / 2 : ℝ) ^ a * ((1 / 2 : ℝ) ^ a) ^ k := by
    intro k
    have : a * (k + 1) ≠ 0 := by positivity
    simp only [lamG, ha, dvd_mul_right, ne_eq, this, not_false_eq_true, and_self, if_true]
    rw [← pow_mul, ← pow_add]; congr 1; ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity)
    (pow_lt_one₀ (by norm_num) (by norm_num) hpos.ne')]
  have h2 : (1 : ℝ) < 2 ^ a := one_lt_pow₀ (by norm_num) hpos.ne'
  have h2' : (2 : ℝ) ^ a - 1 ≠ 0 := by linarith
  rw [one_div_pow]
  field_simp

/-- **Lambert identity.** `∑_{a ∈ A} 1/(2^a - 1) = ∑_m #{d ∣ m : d ∈ A} / 2^m`. (In Lean
`1/(2^0 - 1) = 0` and `Nat.divisors 0 = ∅`, so `0 ∈ A` changes neither side.) -/
private theorem lambert_identity (A : Set ℕ) [DecidablePred (· ∈ A)] :
    ∑' a : A, (1 : ℝ) / (2 ^ a.1 - 1) =
      ∑' m : ℕ, ((((Nat.divisors m).filter (· ∈ A)).card : ℕ) : ℝ) / 2 ^ m := by
  have hs := lamG_summable A
  have hrows : ∑' m : ℕ, ((((Nat.divisors m).filter (· ∈ A)).card : ℕ) : ℝ) / 2 ^ m
      = ∑' m, ∑' a, lamG A (m, a) := by
    refine tsum_congr fun m => ?_
    rw [lamG_row, one_div, inv_pow, div_eq_mul_inv]
  have hcols : ∑' a : A, (1 : ℝ) / (2 ^ a.1 - 1) = ∑' a, ∑' m, lamG A (m, a) := by
    rw [tsum_subtype A (fun a => (1 : ℝ) / (2 ^ a - 1))]
    refine tsum_congr fun a => ?_
    rw [lamG_col]; simp [Set.indicator]
  rw [hrows, hcols]
  have hu : Summable (Function.uncurry fun m a => lamG A (m, a)) := hs
  exact hu.tsum_comm

private lemma omega_eq_card_filter (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n = ((Nat.divisors n).filter (· ∈ {p : ℕ | p.Prime})).card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_divisors, Set.mem_setOf_eq, List.mem_toFinset,
    Nat.mem_primeFactorsList']
  tauto

/-- Equation (1.7) of Tao–Teräväinen: `∑_p 1/(2^p - 1) = ∑_n ω(n)/2^n`. -/
private theorem lambert_primes :
    ∑' p : {p : ℕ | p.Prime}, (1 : ℝ) / (2 ^ p.1 - 1) =
      ∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors n : ℝ) / 2 ^ n := by
  rw [lambert_identity]
  refine tsum_congr fun n => ?_
  rw [omega_eq_card_filter]

private lemma omega_div_summable :
    Summable fun n : ℕ => (ArithmeticFunction.cardDistinctFactors n : ℝ) / 2 ^ n := by
  have hg : Summable fun m : ℕ => ((m : ℝ) ^ 1) * (1 / 2 : ℝ) ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hg
  rw [pow_one, one_div_pow, div_eq_mul_one_div]
  gcongr
  rw [omega_eq_card_filter]
  exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self m)


/-- Elementary step (2) of the primes route (see postmortem #894): if `∑ f(n)/2^n = a/b`, then
for every `N` the binary tail `∑_{k ≥ 0} f(N+1+k)/2^(k+1)` times `b` is an integer. With
`f = ω` this is the reduction Tao–Teräväinen's argument starts from. -/
private theorem tail_mul_den_int (f : ℕ → ℕ) (hs : Summable (fun n => (f n : ℝ) / 2 ^ n))
    (a : ℤ) (b : ℕ) (hb : 0 < b) (h : ∑' n, (f n : ℝ) / 2 ^ n = a / b) (N : ℕ) :
    ∃ z : ℤ, (b : ℝ) * ∑' k, (f (k + (N + 1)) : ℝ) / 2 ^ (k + 1) = z := by
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  have hfin : ∀ n ∈ Finset.range (N + 1), (2 : ℝ) ^ N * ((f n : ℝ) / 2 ^ n) = ((f n * 2 ^ (N - n) : ℕ) : ℝ) := by
    intro n hn
    have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    push_cast
    have : (2 : ℝ) ^ N = 2 ^ (N - n) * 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hn']
    rw [this]; field_simp
  have htail : ∀ k, (2 : ℝ) ^ N * ((f (k + (N + 1)) : ℝ) / 2 ^ (k + (N + 1))) = (f (k + (N + 1)) : ℝ) / 2 ^ (k + 1) := by
    intro k
    have : (2 : ℝ) ^ (k + (N + 1)) = 2 ^ (k + 1) * 2 ^ N := by rw [← pow_add]; ring_nf
    rw [this]; field_simp
  have hI : (2 : ℝ) ^ N * ∑ n ∈ Finset.range (N + 1), (f n : ℝ) / 2 ^ n
      = ((∑ n ∈ Finset.range (N + 1), f n * 2 ^ (N - n) : ℕ) : ℝ) := by
    rw [Finset.mul_sum, Nat.cast_sum]; exact Finset.sum_congr rfl hfin
  have hT : (2 : ℝ) ^ N * ∑' k, (f (k + (N + 1)) : ℝ) / 2 ^ (k + (N + 1))
      = ∑' k, (f (k + (N + 1)) : ℝ) / 2 ^ (k + 1) := by
    rw [← tsum_mul_left]; exact tsum_congr htail
  refine ⟨2 ^ N * a - b * ((∑ n ∈ Finset.range (N + 1), f n * 2 ^ (N - n) : ℕ) : ℤ), ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [← hT]
  have key : (2 : ℝ) ^ N * (a / b) = ((∑ n ∈ Finset.range (N + 1), f n * 2 ^ (N - n) : ℕ) : ℝ)
      + 2 ^ N * ∑' k, (f (k + (N + 1)) : ℝ) / 2 ^ (k + (N + 1)) := by
    rw [← h, ← hsplit, mul_add, hI]
  push_cast at key ⊢
  have : (b : ℝ) * (2 ^ N * (a / b)) = 2 ^ N * a := by field_simp
  linear_combination this - (b : ℝ) * key

/-- Equation (5.1) of Tao–Teräväinen from rationality: if `∑_p 1/(2^p-1) = a/q`, then for every
`N`, `q · ∑_{h ≥ 1} ω(N+h)/2^h` is an integer. -/
private theorem eq_5_1 (a : ℤ) (q : ℕ) (hq : 0 < q)
    (h : ∑' p : {p : ℕ | p.Prime}, (1 : ℝ) / (2 ^ p.1 - 1) = a / q) (N : ℕ) :
    ∃ z : ℤ, (q : ℝ) * ∑' k, (ArithmeticFunction.cardDistinctFactors (k + (N + 1)) : ℝ) / 2 ^ (k + 1) = z :=
  tail_mul_den_int (fun n => ArithmeticFunction.cardDistinctFactors n) omega_div_summable a q hq
    (by rw [← lambert_primes]; exact h) N


private lemma omega_eq_card_pf (n : ℕ) : ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]; rfl

/-- additivity used in (5.2): `ω(p k) + 1_{p ∣ k} = ω(k) + 1` for a prime `p` and `k ≠ 0`. -/
private lemma omega_mul_prime {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ArithmeticFunction.cardDistinctFactors (p * k) + (if p ∣ k then 1 else 0)
      = ArithmeticFunction.cardDistinctFactors k + 1 := by
  rw [omega_eq_card_pf, omega_eq_card_pf, Nat.primeFactors_mul hp.ne_zero hk, hp.primeFactors]
  by_cases h : p ∣ k
  · have hm : p ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, h, hk⟩
    rw [if_pos h, Finset.singleton_union, Finset.insert_eq_of_mem hm]
  · have hm : p ∉ k.primeFactors := fun hm => h (Nat.mem_primeFactors.mp hm).2.1
    rw [if_neg h, Finset.singleton_union, Finset.card_insert_of_notMem hm]

private lemma omega_shift_summable (c : ℕ) :
    Summable fun k : ℕ => (ArithmeticFunction.cardDistinctFactors (k + c) : ℝ) / 2 ^ (k + 1) := by
  have h1 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * (1 / 2 : ℝ) ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have h2 : Summable fun k : ℕ => (c : ℝ) * (1 / 2 : ℝ) ^ k := summable_geometric_two.mul_left _
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (h1.add h2)
  have hw : (ArithmeticFunction.cardDistinctFactors (k + c) : ℝ) ≤ k + c := by
    rw [omega_eq_card_filter]
    exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self _)
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_iff₀ (by positivity), pow_one, one_div_pow]
  have : ((k : ℝ) * (1 / 2 ^ k) + c * (1 / 2 ^ k)) * 2 ^ (k + 1) = 2 * (k + c) := by
    rw [pow_succ]; field_simp
  rw [this]
  have : (0 : ℝ) ≤ k + c := by positivity
  linarith

private lemma ind_summable (f : ℕ → Prop) [DecidablePred f] :
    Summable fun k : ℕ => (if f k then (1 : ℝ) else 0) / 2 ^ (k + 1) := by
  refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_) summable_geometric_two
  rw [one_div_pow]
  have : (0 : ℝ) < 2 ^ k := by positivity
  split_ifs
  · rw [div_le_div_iff_of_pos_left one_pos (by positivity) this]; rw [pow_succ]; linarith
  · simp

/-- Equation (5.2)–(5.3) of Tao–Teräväinen: from the tail congruences (5.1) at `m`, for a prime `p`
and `n = p m`: `q ∑_{h ≥ 1} ω(n + p h)/2^h + q δ_p(n)` is an integer, where
`δ_p(n) = ∑_{h ≥ 1} 1_{p² ∣ n + p h}/2^h`. -/
private theorem eq_5_2 (q : ℕ)
    (hint : ∀ N : ℕ, ∃ z : ℤ,
      (q : ℝ) * ∑' k, (ArithmeticFunction.cardDistinctFactors (k + (N + 1)) : ℝ) / 2 ^ (k + 1) = z)
    {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ∃ z : ℤ, (q : ℝ) * ∑' k, (ArithmeticFunction.cardDistinctFactors (p * m + p * (k + 1)) : ℝ) / 2 ^ (k + 1)
      + (q : ℝ) * ∑' k, (if p ^ 2 ∣ p * m + p * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) = z := by
  obtain ⟨z, hz⟩ := hint m
  refine ⟨z + q, ?_⟩
  have hterm : ∀ k : ℕ,
      (ArithmeticFunction.cardDistinctFactors (p * m + p * (k + 1)) : ℝ) / 2 ^ (k + 1)
      + (if p ^ 2 ∣ p * m + p * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)
      = (ArithmeticFunction.cardDistinctFactors (k + (m + 1)) : ℝ) / 2 ^ (k + 1) + (1 / 2 : ℝ) ^ (k + 1) := by
    intro k
    have he : p * m + p * (k + 1) = p * (k + (m + 1)) := by ring
    have hd : p ^ 2 ∣ p * (k + (m + 1)) ↔ p ∣ k + (m + 1) := by
      rw [pow_two]; exact Nat.mul_dvd_mul_iff_left hp.pos
    have key := omega_mul_prime hp (show k + (m + 1) ≠ 0 by omega)
    rw [he]
    have key' : (ArithmeticFunction.cardDistinctFactors (p * (k + (m + 1))) : ℝ)
        + (if p ^ 2 ∣ p * (k + (m + 1)) then (1 : ℝ) else 0)
        = (ArithmeticFunction.cardDistinctFactors (k + (m + 1)) : ℝ) + 1 := by
      rw [if_congr hd rfl rfl]
      have := congrArg (fun t : ℕ => (t : ℝ)) key
      simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at this
      exact this
    rw [one_div_pow, ← add_div, key', add_div]
  have hG : Summable fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) :=
    (summable_nat_add_iff 1).mpr summable_geometric_two
  have hsA : Summable fun k : ℕ =>
      (ArithmeticFunction.cardDistinctFactors (p * m + p * (k + 1)) : ℝ) / 2 ^ (k + 1) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((omega_shift_summable (m + 1)).add hG)
    have := hterm k
    have h0 : (0 : ℝ) ≤ (if p ^ 2 ∣ p * m + p * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) := by
      split_ifs <;> positivity
    linarith
  have hsB := ind_summable (fun k => p ^ 2 ∣ p * m + p * (k + 1))
  rw [← mul_add, ← hsA.tsum_add hsB, tsum_congr hterm,
    (omega_shift_summable (m + 1)).tsum_add hG]
  have hg : ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1) = 1 := by
    simp_rw [pow_succ]; rw [tsum_mul_right, tsum_geometric_two]; norm_num
  rw [hg, mul_add, hz]; push_cast; ring

/-- `(-1)^{|ε|}` for `ε ∈ {0,1}^K`, as a product of signs. -/
private noncomputable def cubeSgn {K : ℕ} (ε : Fin K → Bool) : ℝ := ∏ i, if ε i then (-1 : ℝ) else 1

private lemma cubeSgn_eq {K : ℕ} (ε : Fin K → Bool) :
    cubeSgn ε = (-1 : ℝ) ^ (Finset.univ.filter fun i => ε i = true).card := by
  unfold cubeSgn
  rw [Finset.prod_ite]; simp

/-- The shifts (5.7): `r_{ε,h} = p₀ h + ∑_k (h - k) ε_k v_k` (coordinates `k = 1, …, K` are
`Fin K` indices `k - 1`). -/
private def cubeShift {K : ℕ} (p0 : ℤ) (v : Fin K → ℤ) (ε : Fin K → Bool) (h : ℕ) : ℤ :=
  p0 * h + ∑ k : Fin K, ((h : ℤ) - (k.1 + 1)) * (if ε k then v k else 0)

/-- (5.7): `r_{ε,h} = p_ε h - ∑_k k ε_k v_k` with `p_ε = p₀ + ∑_k ε_k v_k`. -/
private lemma cubeShift_eq {K : ℕ} (p0 : ℤ) (v : Fin K → ℤ) (ε : Fin K → Bool) (h : ℕ) :
    cubeShift p0 v ε h = (p0 + ∑ k : Fin K, (if ε k then v k else 0)) * h
      - ∑ k : Fin K, ((k.1 : ℤ) + 1) * (if ε k then v k else 0) := by
  unfold cubeShift
  rw [add_mul, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The cancellation behind (5.8): for `1 ≤ h ≤ K` the alternating sum over the cube of any
function of `r_{ε,h}` vanishes, because `r_{ε,h}` does not depend on `ε_h`. -/
private theorem cube_cancel {K : ℕ} (p0 : ℤ) (v : Fin K → ℤ) (g : ℤ → ℝ) {h : ℕ} (h1 : 1 ≤ h) (hK : h ≤ K) :
    ∑ ε : Fin K → Bool, cubeSgn ε * g (cubeShift p0 v ε h) = 0 := by
  let j : Fin K := ⟨h - 1, by omega⟩
  let fl : (Fin K → Bool) → (Fin K → Bool) := fun ε => Function.update ε j (!ε j)
  have hinv : Function.Involutive fl := by
    intro ε; funext i
    by_cases hi : i = j
    · subst hi; simp [fl]
    · simp [fl, Function.update_of_ne hi]
  have hshift : ∀ ε, cubeShift p0 v (fl ε) h = cubeShift p0 v ε h := by
    intro ε; unfold cubeShift; congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = j
    · have : ((h : ℤ) - (k.1 + 1)) = 0 := by rw [hk]; simp only [j]; omega
      rw [this, zero_mul, zero_mul]
    · simp [fl, Function.update_of_ne hk]
  have hsgn : ∀ ε, cubeSgn (fl ε) = - cubeSgn ε := by
    intro ε; unfold cubeSgn
    rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j (fun i => if ε i then (-1 : ℝ) else 1)]
    have hrest : ∏ i ∈ ({j}ᶜ : Finset (Fin K)), (if fl ε i then (-1 : ℝ) else 1)
        = ∏ i ∈ ({j}ᶜ : Finset (Fin K)), (if ε i then (-1 : ℝ) else 1) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have : i ≠ j := by simpa using hi
      simp [fl, Function.update_of_ne this]
    rw [hrest]
    cases hε : ε j <;> simp [fl, hε]
  set S := ∑ ε : Fin K → Bool, cubeSgn ε * g (cubeShift p0 v ε h) with hS
  have : S = -S := by
    let σ : (Fin K → Bool) ≃ (Fin K → Bool) := hinv.toPerm _
    calc S = ∑ ε, cubeSgn (σ ε) * g (cubeShift p0 v (σ ε) h) := (Equiv.sum_comp σ _).symm
      _ = ∑ ε, -(cubeSgn ε * g (cubeShift p0 v ε h)) := by
          refine Finset.sum_congr rfl fun ε _ => ?_
          show cubeSgn (fl ε) * g (cubeShift p0 v (fl ε) h) = _
          rw [hsgn, hshift]; ring
      _ = -S := by rw [Finset.sum_neg_distrib]
  linarith

private lemma omega_bound_summable (f : ℕ → ℕ) (a b : ℕ) (hf : ∀ k, f k ≤ a + b * k) :
    Summable fun k : ℕ => (ArithmeticFunction.cardDistinctFactors (f k) : ℝ) / 2 ^ (k + 1) := by
  have h0 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * (1 / 2 : ℝ) ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have h1 : Summable fun k : ℕ => (b : ℝ) * (((k : ℝ) ^ 1) * (1 / 2 : ℝ) ^ k) := h0.mul_left _
  have h2 : Summable fun k : ℕ => (a : ℝ) * (1 / 2 : ℝ) ^ k := summable_geometric_two.mul_left _
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (h2.add h1)
  have hw : (ArithmeticFunction.cardDistinctFactors (f k) : ℝ) ≤ a + b * k := by
    rw [omega_eq_card_filter]
    exact_mod_cast (Finset.card_filter_le _ _).trans ((Nat.card_divisors_le_self (f k)).trans (hf k))
  rw [div_le_iff₀ (by positivity), pow_one, one_div_pow]
  have : ((a : ℝ) * (1 / 2 ^ k) + b * (k * (1 / 2 ^ k))) * 2 ^ (k + 1) = 2 * (a + b * k) := by
    rw [pow_succ]; field_simp
  rw [this]
  have : (0 : ℝ) ≤ a + b * k := by positivity
  linarith

/-- Equation (5.8) of Tao–Teräväinen, from (5.1) for all `N`. Hypotheses: `P ε = p_ε` are primes
(5.4), and `n - ∑_k k ε_k v_k = p_ε m_ε` with `m_ε ∈ ℕ` (this is (5.5) together with (5.6)).
Conclusion: `q ∑_{h ≥ 1} ∑_ε (-1)^{|ε|} ω(n + r_{ε,h+K}) / 2^{h+K}
  + q ∑_ε (-1)^{|ε|} δ_{p_ε}(n - ∑_k k ε_k v_k)` is an integer (indices `h = k + 1`). -/
private theorem eq_5_8 (q : ℕ)
    (hint : ∀ N : ℕ, ∃ z : ℤ,
      (q : ℝ) * ∑' k, (ArithmeticFunction.cardDistinctFactors (k + (N + 1)) : ℝ) / 2 ^ (k + 1) = z)
    {K : ℕ} (p0 : ℤ) (v : Fin K → ℤ) (P : (Fin K → Bool) → ℕ)
    (hP : ∀ ε, (P ε : ℤ) = p0 + ∑ k : Fin K, (if ε k then v k else 0))
    (hprime : ∀ ε, (P ε).Prime) (n : ℤ) (m : (Fin K → Bool) → ℕ)
    (hm : ∀ ε, n - ∑ k : Fin K, ((k.1 : ℤ) + 1) * (if ε k then v k else 0) = P ε * m ε) :
    ∃ z : ℤ,
      (q : ℝ) * ∑' k, (∑ ε : Fin K → Bool, cubeSgn ε *
          (ArithmeticFunction.cardDistinctFactors (n + cubeShift p0 v ε (k + K + 1)).toNat : ℝ))
          / 2 ^ (k + K + 1)
      + (q : ℝ) * ∑ ε : Fin K → Bool, cubeSgn ε *
          ∑' k, (if P ε ^ 2 ∣ P ε * m ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) = z := by
  -- the per-vertex congruences (5.2)
  have hz : ∀ ε, ∃ z : ℤ,
      (q : ℝ) * ∑' k, (ArithmeticFunction.cardDistinctFactors (P ε * m ε + P ε * (k + 1)) : ℝ) / 2 ^ (k + 1)
      + (q : ℝ) * ∑' k, (if P ε ^ 2 ∣ P ε * m ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) = z :=
    fun ε => eq_5_2 q hint (hprime ε) (m ε)
  choose z hz using hz
  -- the shift identity n + r_{ε,h} = p_ε m_ε + p_ε h
  have hsh : ∀ ε (h : ℕ), (n + cubeShift p0 v ε h).toNat = P ε * m ε + P ε * h := by
    intro ε h
    have : n + cubeShift p0 v ε h = ((P ε * m ε + P ε * h : ℕ) : ℤ) := by
      rw [cubeShift_eq, ← hP ε]; push_cast; linear_combination hm ε
    rw [this, Int.toNat_natCast]
  let a : (Fin K → Bool) → ℕ → ℝ := fun ε k =>
    (ArithmeticFunction.cardDistinctFactors (P ε * m ε + P ε * (k + 1)) : ℝ) / 2 ^ (k + 1)
  have ha : ∀ ε, Summable (a ε) := fun ε =>
    omega_bound_summable (fun k => P ε * m ε + P ε * (k + 1)) (P ε * m ε + P ε) (P ε)
      (fun k => by ring_nf; omega)
  let F : ℕ → ℝ := fun k => ∑ ε : Fin K → Bool, cubeSgn ε * a ε k
  have hF : Summable F := summable_sum fun ε _ => (ha ε).mul_left _
  -- the first K terms cancel (5.8)
  have hfirst : ∑ i ∈ Finset.range K, F i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hiK : i + 1 ≤ K := Finset.mem_range.mp hi
    have := cube_cancel p0 v (fun t => (ArithmeticFunction.cardDistinctFactors (n + t).toNat : ℝ) / 2 ^ (i + 1))
      (h := i + 1) (by omega) hiK
    simp only [F, a]
    rw [← this]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [hsh]
  have htail : ∀ k, F (k + K) = (∑ ε : Fin K → Bool, cubeSgn ε *
      (ArithmeticFunction.cardDistinctFactors (n + cubeShift p0 v ε (k + K + 1)).toNat : ℝ))
      / 2 ^ (k + K + 1) := by
    intro k
    simp only [F, a]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [hsh, mul_div_assoc]
  have hsum := hF.sum_add_tsum_nat_add K
  rw [hfirst, zero_add] at hsum
  simp_rw [htail] at hsum
  rw [hsum]
  have hswap : ∑' k, F k = ∑ ε : Fin K → Bool, cubeSgn ε * ∑' k, a ε k := by
    simp only [F]
    rw [Summable.tsum_finsetSum fun ε _ => (ha ε).mul_left _]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [tsum_mul_left]
  rw [hswap]
  refine ⟨∑ ε : Fin K → Bool, (-1 : ℤ) ^ (Finset.univ.filter fun i => ε i = true).card * z ε, ?_⟩
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [← hz ε, cubeSgn_eq]
  simp only [a]
  ring

/-- Rationality of `∑_p 1/(2^p - 1)` implies (5.8) for every prime cube and every admissible `n`:
S1–S4 of the route map (annex on `variant-6b364d2b`) chained together. -/
private theorem rational_imp_5_8 (a : ℤ) (q : ℕ) (hq : 0 < q)
    (h : ∑' p : {p : ℕ | p.Prime}, (1 : ℝ) / (2 ^ p.1 - 1) = a / q)
    {K : ℕ} (p0 : ℤ) (v : Fin K → ℤ) (P : (Fin K → Bool) → ℕ)
    (hP : ∀ ε, (P ε : ℤ) = p0 + ∑ k : Fin K, (if ε k then v k else 0))
    (hprime : ∀ ε, (P ε).Prime) (n : ℤ) (m : (Fin K → Bool) → ℕ)
    (hm : ∀ ε, n - ∑ k : Fin K, ((k.1 : ℤ) + 1) * (if ε k then v k else 0) = P ε * m ε) :
    ∃ z : ℤ,
      (q : ℝ) * ∑' k, (∑ ε : Fin K → Bool, cubeSgn ε *
          (ArithmeticFunction.cardDistinctFactors (n + cubeShift p0 v ε (k + K + 1)).toNat : ℝ))
          / 2 ^ (k + K + 1)
      + (q : ℝ) * ∑ ε : Fin K → Bool, cubeSgn ε *
          ∑' k, (if P ε ^ 2 ∣ P ε * m ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) = z :=
  eq_5_8 q (fun N => eq_5_1 a q hq h N) p0 v P hP hprime n m hm

/-- `2^{ω(n)} ≤ n` for `n ≠ 0`, i.e. `ω(n) ≤ log₂ n`: the crude bound `ω(n) ≪ log n` of §5.8. -/
private theorem two_pow_omega_le {n : ℕ} (hn : n ≠ 0) : 2 ^ ArithmeticFunction.cardDistinctFactors n ≤ n := by
  rw [omega_eq_card_pf]
  calc 2 ^ n.primeFactors.card = ∏ p ∈ n.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- `e(t) = exp(2πit)`. -/
private noncomputable def ee (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private lemma ee_norm (t : ℝ) : ‖ee t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma ee_int (z : ℤ) : ee z = 1 := by
  unfold ee
  rw [← Complex.exp_int_mul_two_pi_mul_I z]; congr 1; push_cast; ring

private lemma ee_re (t : ℝ) : (ee t).re = Real.cos (2 * Real.pi * t) :=
  Complex.exp_ofReal_mul_I_re _

private lemma ee_conj (t : ℝ) : (starRingEnd ℂ) (ee t) = ee (-t) := by
  unfold ee; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

/-- `‖e(t) - 1‖ ≤ 2π|t|`. -/
private lemma ee_sub_one (t : ℝ) : ‖ee t - 1‖ ≤ 2 * Real.pi * |t| := by
  set x : ℝ := 2 * Real.pi * t with hx
  have hre : (ee t - 1).re = Real.cos x - 1 := by
    rw [Complex.sub_re, ee_re, Complex.one_re]
  have him : (ee t - 1).im = Real.sin x := by
    simp only [Complex.sub_im, Complex.one_im, sub_zero, ee]
    exact Complex.exp_ofReal_mul_I_im _
  have hsq : ‖ee t - 1‖ ^ 2 ≤ x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
    have h2 := Real.sin_sq_add_cos_sq x
    nlinarith
  have := (sq_le_sq.mp hsq)
  rw [abs_of_nonneg (norm_nonneg _)] at this
  calc ‖ee t - 1‖ ≤ |x| := this
    _ = 2 * Real.pi * |t| := by
      rw [hx, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- `∑∑ (a_i - a_j)^2 = 2N ∑ a^2 - 2 (∑ a)^2`. -/
private lemma sum_sum_sub_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2
      = 2 * (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 - 2 * (∑ i ∈ s, a i) ^ 2 := by
  have e1 : ∀ i j, (a i - a j) ^ 2 = a i ^ 2 + a j ^ 2 - 2 * (a i * a j) := fun i j => by ring
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  rw [← Finset.sum_mul]; ring

/-- The variance step of (5.20): for `|X| ≤ 1/4` on a finite nonempty set, with `n` uniform,
`|E e(X)|^2 ≤ 1 - 16 Var X`. -/
private lemma norm_avg_ee_sq_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (X : ι → ℝ)
    (hX : ∀ i ∈ s, |X i| ≤ 1 / 4) :
    ‖((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (X i)‖ ^ 2
      ≤ 1 - 16 * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X i ^ 2 - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X i) ^ 2) := by
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  set S : ℂ := ∑ i ∈ s, ee (X i) with hS
  have hnorm : ‖S‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, Real.cos (2 * Real.pi * (X i - X j)) := by
    have h1 : ((‖S‖ ^ 2 : ℝ) : ℂ) = S * (starRingEnd ℂ) S := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : S * (starRingEnd ℂ) S = ∑ i ∈ s, ∑ j ∈ s, ee (X i - X j) := by
      rw [hS, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [ee_conj, sub_eq_add_neg, ee_add]
    have h3 := congrArg Complex.re (h1.trans h2)
    rw [Complex.ofReal_re] at h3
    rw [h3, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => ee_re _
  have hcos : ∀ i ∈ s, ∀ j ∈ s,
      Real.cos (2 * Real.pi * (X i - X j)) ≤ 1 - 8 * (X i - X j) ^ 2 := by
    intro i hi j hj
    have hij : |X i - X j| ≤ 1 / 2 := by
      have := abs_sub (X i) (X j); linarith [hX i hi, hX j hj]
    have hpi : |2 * Real.pi * (X i - X j)| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    have := Real.cos_le_one_sub_mul_cos_sq hpi
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    calc Real.cos (2 * Real.pi * (X i - X j)) ≤ 1 - 2 / Real.pi ^ 2 * (2 * Real.pi * (X i - X j)) ^ 2 :=
          this
      _ = 1 - 8 * (X i - X j) ^ 2 := by field_simp; ring
  have hsum : ‖S‖ ^ 2 ≤ (s.card : ℝ) ^ 2 - 8 * (2 * (s.card : ℝ) * ∑ i ∈ s, X i ^ 2
      - 2 * (∑ i ∈ s, X i) ^ 2) := by
    rw [hnorm, ← sum_sum_sub_sq]
    calc ∑ i ∈ s, ∑ j ∈ s, Real.cos (2 * Real.pi * (X i - X j))
        ≤ ∑ i ∈ s, ∑ j ∈ s, (1 - 8 * (X i - X j) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hcos i hi j hj
      _ = (s.card : ℝ) ^ 2 - 8 * ∑ i ∈ s, ∑ j ∈ s, (X i - X j) ^ 2 := by
          simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
            ← Finset.mul_sum]
          ring
  rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  have hN2 : (0 : ℝ) < (s.card : ℝ) ^ 2 := by positivity
  rw [inv_pow, inv_mul_le_iff₀ hN2]
  have : (s.card : ℝ) ^ 2 * (1 - 16 * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X i ^ 2
      - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X i) ^ 2))
      = (s.card : ℝ) ^ 2 - 8 * (2 * (s.card : ℝ) * ∑ i ∈ s, X i ^ 2
      - 2 * (∑ i ∈ s, X i) ^ 2) := by
    field_simp; ring
  rw [this]; exact hsum

/-- The product step of (5.20): `|∏_p E e(X_p)| ≤ exp(-8 ∑_p Var X_p)`. -/
private lemma norm_prod_avg_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (S1 : Finset ℕ)
    (X : ℕ → ι → ℝ) (hX : ∀ p ∈ S1, ∀ i ∈ s, |X p i| ≤ 1 / 4) :
    ‖∏ p ∈ S1, ((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (X p i)‖
      ≤ Real.exp (-8 * ∑ p ∈ S1, ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i ^ 2
          - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i) ^ 2)) := by
  have hsq : ‖∏ p ∈ S1, ((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (X p i)‖ ^ 2
      ≤ Real.exp (-8 * ∑ p ∈ S1, ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i ^ 2
          - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i) ^ 2)) ^ 2 := by
    rw [norm_prod, ← Finset.prod_pow, sq, ← Real.exp_add, Finset.mul_sum, ← Finset.sum_add_distrib,
      Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
    refine (norm_avg_ee_sq_le s hs (X p) (hX p hp)).trans ?_
    have := Real.add_one_le_exp (-8 * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i ^ 2
          - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i) ^ 2) + -8 * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i ^ 2
          - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i) ^ 2))
    linarith
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos (Real.exp_pos _)] at this

/-- S5–S7 assembled: if every `Y + C₀ + W` is an integer, `E|W| ≤ δ`, the decorrelation defect is
at most `δ`, `|X_p| ≤ 1/4` and `∑ Var X_p ≥ c₀`, then `1 - 8δ ≤ exp(-8c₀)`. -/
private lemma assembly_core {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (S1 : Finset ℕ)
    (X : ℕ → ι → ℝ) (W : ι → ℝ) (C0 δ c0 : ℝ)
    (hint : ∀ i ∈ s, ∃ z : ℤ, (∑ p ∈ S1, X p i) + C0 + W i = z)
    (hX : ∀ p ∈ S1, ∀ i ∈ s, |X p i| ≤ 1 / 4)
    (hW : (s.card : ℝ)⁻¹ * ∑ i ∈ s, |W i| ≤ δ)
    (hdec : ‖((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (∑ p ∈ S1, X p i)
        - ∏ p ∈ S1, ((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (X p i)‖ ≤ δ)
    (hvar : c0 ≤ ∑ p ∈ S1, ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i ^ 2
          - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i) ^ 2)) :
    1 - 8 * δ ≤ Real.exp (-8 * c0) := by
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hδ : 0 ≤ δ := le_trans (by positivity) hW
  -- each phase is `e(-C₀) e(-W)`
  have hpt : ∀ i ∈ s, ‖ee (∑ p ∈ S1, X p i) - ee (-C0)‖ ≤ 2 * Real.pi * |W i| := by
    intro i hi
    obtain ⟨z, hz⟩ := hint i hi
    have : ee (∑ p ∈ S1, X p i) = ee (-C0) * ee (-W i) := by
      have e1 : (∑ p ∈ S1, X p i) = (z : ℝ) + -C0 + -W i := by linarith
      rw [e1, ee_add, ee_add, ee_int, one_mul]
    rw [this, ← mul_sub_one, norm_mul, ee_norm, one_mul]
    have := ee_sub_one (-W i); rwa [abs_neg] at this
  set A : ℂ := ((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (∑ p ∈ S1, X p i) with hA
  have hA1 : ‖A - ee (-C0)‖ ≤ 2 * Real.pi * δ := by
    have hc : ee (-C0) = ((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (-C0) := by
      have : (s.card : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, Complex.ofReal_natCast,
        inv_mul_cancel₀ this, one_mul]
    rw [hA, hc, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hN]
    calc (s.card : ℝ)⁻¹ * ‖∑ i ∈ s, (ee (∑ p ∈ S1, X p i) - ee (-C0))‖
        ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, 2 * Real.pi * |W i| := by
          exact mul_le_mul_of_nonneg_left
            ((norm_sum_le _ _).trans (Finset.sum_le_sum hpt)) (inv_nonneg.mpr hN.le)
      _ = 2 * Real.pi * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, |W i|) := by rw [← Finset.mul_sum]; ring
      _ ≤ 2 * Real.pi * δ := mul_le_mul_of_nonneg_left hW (by linarith [Real.pi_pos])
  have hA2 : 1 - 2 * Real.pi * δ ≤ ‖A‖ := by
    have := norm_sub_norm_le (ee (-C0)) (ee (-C0) - A)
    rw [sub_sub_cancel, ee_norm, norm_sub_rev] at this
    linarith
  have hP := norm_prod_avg_le s hs S1 X hX
  have hP2 : ‖A‖ - δ ≤ ‖∏ p ∈ S1, ((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (X p i)‖ := by
    have := norm_sub_norm_le A (A - ∏ p ∈ S1, ((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (X p i))
    rw [sub_sub_cancel] at this
    linarith
  have hexp : Real.exp (-8 * ∑ p ∈ S1, ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i ^ 2
          - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X p i) ^ 2)) ≤ Real.exp (-8 * c0) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  nlinarith

/-- Independence: the average over `Ns^{S₁}` of a product is the product of averages. -/
private lemma sum_pi_prod {R : Type*} [CommSemiring R] (S1 : Finset ℕ) (Ns : Finset ℤ)
    (f : ℕ → ℤ → R) :
    ∑ ω ∈ Fintype.piFinset (fun _ : S1 => Ns), ∏ p : S1, f p (ω p) = ∏ p ∈ S1, ∑ n ∈ Ns, f p n := by
  rw [← Finset.prod_univ_sum (fun _ : S1 => Ns) (fun p n => f p n)]
  exact Finset.prod_coe_sort S1 (fun p => ∑ n ∈ Ns, f p n)

private lemma card_pi (S1 : Finset ℕ) (Ns : Finset ℤ) :
    ((Fintype.piFinset (fun _ : S1 => Ns)).card : ℝ) = (Ns.card : ℝ) ^ S1.card := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe]; push_cast; rfl

/-- `E' e(∑ X'_p) = ∏ E e(X_p)` for independent copies. -/
private lemma avg_pi_ee (S1 : Finset ℕ) (Ns : Finset ℤ) (X : ℕ → ℤ → ℝ) :
    (((Fintype.piFinset (fun _ : S1 => Ns)).card : ℝ) : ℂ)⁻¹
        * ∑ ω ∈ Fintype.piFinset (fun _ : S1 => Ns), ee (∑ p : S1, X p (ω p))
      = ∏ p ∈ S1, ((Ns.card : ℝ) : ℂ)⁻¹ * ∑ n ∈ Ns, ee (X p n) := by
  have hprod : ∀ ω : S1 → ℤ, ee (∑ p : S1, X p (ω p)) = ∏ p : S1, ee (X p (ω p)) := by
    intro ω
    unfold ee
    rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [hprod]
  rw [sum_pi_prod S1 Ns (fun p n => ee (X p n)), card_pi, Finset.prod_mul_distrib, Finset.prod_const]
  push_cast
  rw [inv_pow]

/-- `E' exp(c ∑ X'_p) = ∏ E exp(c X_p)`. -/
private lemma avg_pi_exp (S1 : Finset ℕ) (Ns : Finset ℤ) (X : ℕ → ℤ → ℝ) (c : ℝ) :
    ((Fintype.piFinset (fun _ : S1 => Ns)).card : ℝ)⁻¹
        * ∑ ω ∈ Fintype.piFinset (fun _ : S1 => Ns), Real.exp (c * ∑ p : S1, X p (ω p))
      = ∏ p ∈ S1, (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, Real.exp (c * X p n) := by
  have hprod : ∀ ω : S1 → ℤ, Real.exp (c * ∑ p : S1, X p (ω p)) = ∏ p : S1, Real.exp (c * X p (ω p)) := by
    intro ω; rw [← Real.exp_sum, Finset.mul_sum]
  simp_rw [hprod]
  rw [sum_pi_prod S1 Ns (fun p n => Real.exp (c * X p n)), card_pi, Finset.prod_mul_distrib,
    Finset.prod_const, inv_pow]

/-- `t^M/M! ≤ e^t + e^{-t}` for even `M`. -/
private lemma pow_div_fact_le_exp_add {M : ℕ} (hM : Even M) (t : ℝ) :
    t ^ M / M.factorial ≤ Real.exp t + Real.exp (-t) := by
  have h1 := Real.pow_div_factorial_le_exp |t| (abs_nonneg t) M
  have h2 : t ^ M = |t| ^ M := (hM.pow_abs t).symm
  rw [h2]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht] at h1 ⊢; linarith [Real.exp_pos (-t)]
  · rw [abs_of_nonpos ht] at h1 ⊢; linarith [Real.exp_pos t]

/-- The sharp Taylor bound for `e(y)`, from the one for `exp(ix)`. -/
private lemma ee_taylor (htay : ∀ (x : ℝ) (M : ℕ), ‖Complex.exp ((x : ℂ) * Complex.I)
      - ∑ m ∈ Finset.range M, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖
      ≤ |x| ^ M / M.factorial) (M : ℕ) (y : ℝ) :
    ‖ee y - ∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ) * (y : ℂ) ^ m‖
      ≤ (2 * Real.pi) ^ M / M.factorial * |y| ^ M := by
  have h := htay (2 * Real.pi * y) M
  have e1 : ∑ m ∈ Finset.range M, (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ) * (y : ℂ) ^ m :=
    Finset.sum_congr rfl fun m _ => by push_cast; ring
  rw [e1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), mul_pow] at h
  unfold ee
  calc _ ≤ (2 * Real.pi) ^ M * |y| ^ M / M.factorial := h
    _ = _ := by ring

/-- An average of `e(Z)` is the Taylor part plus the average remainder. -/
private lemma avg_ee_split {γ : Type*} (u : Finset γ) (Z : γ → ℝ) (M : ℕ) :
    ((u.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ u, ee (Z i)
      = ∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)
          * (((u.card : ℝ)⁻¹ * ∑ i ∈ u, Z i ^ m : ℝ) : ℂ)
        + ((u.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ u, (ee (Z i) - ∑ m ∈ Finset.range M,
            (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ) * (Z i : ℂ) ^ m) := by
  have hC : ((u.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ u, ∑ m ∈ Finset.range M,
        (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ) * (Z i : ℂ) ^ m
      = ∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)
          * (((u.card : ℝ)⁻¹ * ∑ i ∈ u, Z i ^ m : ℝ) : ℂ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum]; push_cast; ring
  rw [Finset.sum_sub_distrib, mul_sub, hC]; ring

private lemma norm_avg_rem_le {γ : Type*} (u : Finset γ) (Z : γ → ℝ) (M : ℕ)
    (htay : ∀ (x : ℝ) (M : ℕ), ‖Complex.exp ((x : ℂ) * Complex.I)
      - ∑ m ∈ Finset.range M, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖
      ≤ |x| ^ M / M.factorial) :
    ‖((u.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ u, (ee (Z i) - ∑ m ∈ Finset.range M,
            (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ) * (Z i : ℂ) ^ m)‖
      ≤ (2 * Real.pi) ^ M / M.factorial * ((u.card : ℝ)⁻¹ * ∑ i ∈ u, |Z i| ^ M) := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc (u.card : ℝ)⁻¹ * ‖∑ i ∈ u, (ee (Z i) - ∑ m ∈ Finset.range M,
            (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ) * (Z i : ℂ) ^ m)‖
      ≤ (u.card : ℝ)⁻¹ * ∑ i ∈ u, (2 * Real.pi) ^ M / M.factorial * |Z i| ^ M :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun i _ => ee_taylor htay M (Z i))) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

private lemma norm_coef (m : ℕ) :
    ‖(2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)‖ = (2 * Real.pi) ^ m / m.factorial := by
  rw [norm_div, norm_pow, Complex.norm_natCast, norm_mul, Complex.norm_I, mul_one, norm_mul,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The comparison at the start of §5.4: `|E e(Y) - E e(Y')| ≤ ∑_{m<M} (2π)^m/m! |E Y^m - E Y'^m|
+ (2π)^M/M! (E|Y|^M + E|Y'|^M)`. -/
private lemma avg_ee_compare {α β : Type*} (s : Finset α) (t : Finset β) (Y : α → ℝ) (Y' : β → ℝ)
    (M : ℕ) (htay : ∀ (x : ℝ) (M : ℕ), ‖Complex.exp ((x : ℂ) * Complex.I)
      - ∑ m ∈ Finset.range M, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖
      ≤ |x| ^ M / M.factorial) :
    ‖((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, ee (Y i) - ((t.card : ℝ) : ℂ)⁻¹ * ∑ j ∈ t, ee (Y' j)‖
      ≤ ∑ m ∈ Finset.range M, (2 * Real.pi) ^ m / m.factorial
          * |(s.card : ℝ)⁻¹ * ∑ i ∈ s, Y i ^ m - (t.card : ℝ)⁻¹ * ∑ j ∈ t, Y' j ^ m|
        + (2 * Real.pi) ^ M / M.factorial * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, |Y i| ^ M
          + (t.card : ℝ)⁻¹ * ∑ j ∈ t, |Y' j| ^ M) := by
  rw [avg_ee_split s Y M, avg_ee_split t Y' M]
  set Rs := ((s.card : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, (ee (Y i) - ∑ m ∈ Finset.range M,
            (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ) * (Y i : ℂ) ^ m)
  set Rt := ((t.card : ℝ) : ℂ)⁻¹ * ∑ j ∈ t, (ee (Y' j) - ∑ m ∈ Finset.range M,
            (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ) * (Y' j : ℂ) ^ m)
  have hRs := norm_avg_rem_le s Y M htay
  have hRt := norm_avg_rem_le t Y' M htay
  have hmain : ‖∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)
          * (((s.card : ℝ)⁻¹ * ∑ i ∈ s, Y i ^ m : ℝ) : ℂ)
        - ∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)
          * (((t.card : ℝ)⁻¹ * ∑ j ∈ t, Y' j ^ m : ℝ) : ℂ)‖
      ≤ ∑ m ∈ Finset.range M, (2 * Real.pi) ^ m / m.factorial
          * |(s.card : ℝ)⁻¹ * ∑ i ∈ s, Y i ^ m - (t.card : ℝ)⁻¹ * ∑ j ∈ t, Y' j ^ m| := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [← mul_sub, norm_mul, norm_coef, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set A := ∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)
          * (((s.card : ℝ)⁻¹ * ∑ i ∈ s, Y i ^ m : ℝ) : ℂ)
        - ∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)
          * (((t.card : ℝ)⁻¹ * ∑ j ∈ t, Y' j ^ m : ℝ) : ℂ) with hA
  have h3 : ‖A + Rs + -Rt‖ ≤ ‖A‖ + ‖Rs‖ + ‖-Rt‖ := norm_add₃_le
  rw [norm_neg] at h3
  have heq : ‖(∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)
          * (((s.card : ℝ)⁻¹ * ∑ i ∈ s, Y i ^ m : ℝ) : ℂ) + Rs)
        - (∑ m ∈ Finset.range M, (2 * Real.pi * Complex.I) ^ m / (m.factorial : ℂ)
          * (((t.card : ℝ)⁻¹ * ∑ j ∈ t, Y' j ^ m : ℝ) : ℂ) + Rt)‖ = ‖A + Rs + -Rt‖ := by
    congr 1; rw [hA]; ring
  rw [heq]
  linarith

/-- (5.16)–(5.17) give the decorrelation: `|E e(∑ X_p) - ∏ E e(X_p)| ≤ 2κ₄ + 2κ₅`, with `X'_p`
independent copies (uniform on `Ns^{S₁}`) and `e = exp 1` in `κ₅`. -/
private lemma decor_bound (Ns : Finset ℤ) (S1 : Finset ℕ) (X : ℕ → ℤ → ℝ) (M : ℕ) (hM : Even M)
    (htay : ∀ (x : ℝ) (M : ℕ), ‖Complex.exp ((x : ℂ) * Complex.I)
      - ∑ m ∈ Finset.range M, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖
      ≤ |x| ^ M / M.factorial) :
    ‖((Ns.card : ℝ) : ℂ)⁻¹ * ∑ n ∈ Ns, ee (∑ p ∈ S1, X p n)
        - ∏ p ∈ S1, ((Ns.card : ℝ) : ℂ)⁻¹ * ∑ n ∈ Ns, ee (X p n)‖
      ≤ 2 * (∑ m ∈ Finset.range (M + 1), (2 * Real.pi) ^ m / m.factorial
          * |(Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (∑ p ∈ S1, X p n) ^ m
            - ((Fintype.piFinset (fun _ : S1 => Ns)).card : ℝ)⁻¹
              * ∑ ω ∈ Fintype.piFinset (fun _ : S1 => Ns), (∑ p : S1, X p (ω p)) ^ m|)
        + 2 * ((∏ p ∈ S1, (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns,
              Real.exp (2 * Real.pi * Real.exp 1 * X p n)
            + ∏ p ∈ S1, (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns,
              Real.exp (-(2 * Real.pi * Real.exp 1) * X p n)) / Real.exp 1 ^ M) := by
  set Ω := Fintype.piFinset (fun _ : S1 => Ns) with hΩ
  rw [← avg_pi_ee S1 Ns X]
  have hc := avg_ee_compare Ns Ω (fun n => ∑ p ∈ S1, X p n) (fun ω => ∑ p : S1, X p (ω p)) M htay
  beta_reduce at hc
  -- |Y|^M = Y^M
  have habs : ∀ y : ℝ, |y| ^ M = y ^ M := fun y => hM.pow_abs y
  simp only [habs] at hc
  -- the kappa_5 bound on the independent M-th moment
  have hk5 : (2 * Real.pi) ^ M / M.factorial
        * ((Ω.card : ℝ)⁻¹ * ∑ ω ∈ Ω, (∑ p : S1, X p (ω p)) ^ M)
      ≤ (∏ p ∈ S1, (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, Real.exp (2 * Real.pi * Real.exp 1 * X p n)
          + ∏ p ∈ S1, (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns,
              Real.exp (-(2 * Real.pi * Real.exp 1) * X p n)) / Real.exp 1 ^ M := by
    rw [← avg_pi_exp S1 Ns X, ← avg_pi_exp S1 Ns X, ← mul_add, ← Finset.sum_add_distrib]
    have hE : (0 : ℝ) < Real.exp 1 ^ M := by positivity
    rw [mul_div_assoc, Finset.sum_div, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    have := pow_div_fact_le_exp_add hM (2 * Real.pi * Real.exp 1 * ∑ p : S1, X p (ω p))
    rw [le_div_iff₀ hE]
    calc (2 * Real.pi) ^ M / M.factorial * (∑ p : S1, X p (ω p)) ^ M * Real.exp 1 ^ M
        = (2 * Real.pi * Real.exp 1 * ∑ p : S1, X p (ω p)) ^ M / M.factorial := by ring
      _ ≤ _ := by rw [neg_mul]; exact this
  have hsplit : (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (∑ p ∈ S1, X p n) ^ M
      ≤ |(Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (∑ p ∈ S1, X p n) ^ M
          - (Ω.card : ℝ)⁻¹ * ∑ ω ∈ Ω, (∑ p : S1, X p (ω p)) ^ M|
        + (Ω.card : ℝ)⁻¹ * ∑ ω ∈ Ω, (∑ p : S1, X p (ω p)) ^ M := by
    have := le_abs_self ((Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (∑ p ∈ S1, X p n) ^ M
          - (Ω.card : ℝ)⁻¹ * ∑ ω ∈ Ω, (∑ p : S1, X p (ω p)) ^ M)
    linarith
  rw [Finset.sum_range_succ]
  have hcoef : (0 : ℝ) ≤ (2 * Real.pi) ^ M / M.factorial := by positivity
  have hterms : 0 ≤ ∑ m ∈ Finset.range M, (2 * Real.pi) ^ m / m.factorial
          * |(Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (∑ p ∈ S1, X p n) ^ m
            - (Ω.card : ℝ)⁻¹ * ∑ ω ∈ Ω, (∑ p : S1, X p (ω p)) ^ m| :=
    Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (abs_nonneg _)
  have hlast : 0 ≤ (2 * Real.pi) ^ M / M.factorial
          * |(Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (∑ p ∈ S1, X p n) ^ M
            - (Ω.card : ℝ)⁻¹ * ∑ ω ∈ Ω, (∑ p : S1, X p (ω p)) ^ M| :=
    mul_nonneg hcoef (abs_nonneg _)
  have := mul_le_mul_of_nonneg_left hsplit hcoef
  nlinarith

private lemma taylor_term_deriv (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((s : ℂ) * Complex.I) ^ (m + 1) / ((m + 1).factorial : ℂ))
      (Complex.I * (((t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))) t := by
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) (1 * Complex.I) t :=
    ((hasDerivAt_id t).ofReal_comp).mul_const Complex.I
  have h1 := (h0.pow (m + 1)).div_const ((m + 1).factorial : ℂ)
  refine h1.congr_deriv ?_
  rw [Nat.factorial_succ]
  push_cast
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hm : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp

private lemma taylor_deriv (M : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)
        - ∑ m ∈ Finset.range (M + 1), ((s : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))
      (Complex.I * (Complex.exp ((t : ℂ) * Complex.I)
        - ∑ m ∈ Finset.range M, ((t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))) t := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * (1 * Complex.I)) t :=
    (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp
  have hs : HasDerivAt (fun s : ℝ => ∑ m ∈ Finset.range M,
        ((s : ℂ) * Complex.I) ^ (m + 1) / ((m + 1).factorial : ℂ))
      (∑ m ∈ Finset.range M, Complex.I * (((t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))) t :=
    HasDerivAt.fun_sum fun m _ => taylor_term_deriv m t
  have hfun : (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)
        - ∑ m ∈ Finset.range (M + 1), ((s : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))
      = fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I) - (∑ m ∈ Finset.range M,
        ((s : ℂ) * Complex.I) ^ (m + 1) / ((m + 1).factorial : ℂ) + 1) := by
    funext s; rw [Finset.sum_range_succ']; simp
  rw [hfun]
  refine (he.sub (hs.add_const 1)).congr_deriv ?_
  rw [← Finset.mul_sum]; ring

private lemma taylor_nonneg (M : ℕ) : ∀ x : ℝ, 0 ≤ x →
    ‖Complex.exp ((x : ℂ) * Complex.I)
      - ∑ m ∈ Finset.range M, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖
      ≤ x ^ M / M.factorial := by
  induction M with
  | zero =>
    intro x _
    simp [Complex.norm_exp_ofReal_mul_I]
  | succ M ih =>
    intro x hx
    have hB : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s ^ (M + 1) / ((M + 1).factorial : ℝ))
        (t ^ M / (M.factorial : ℝ)) t := by
      intro t
      refine ((hasDerivAt_pow (M + 1) t).div_const ((M + 1).factorial : ℝ)).congr_deriv ?_
      rw [Nat.factorial_succ]; push_cast
      have hf : (M.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos M).ne'
      field_simp
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)
        - ∑ m ∈ Finset.range (M + 1), ((s : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))
      (a := 0) (b := x)
      (f' := fun t => Complex.I * (Complex.exp ((t : ℂ) * Complex.I)
        - ∑ m ∈ Finset.range M, ((t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)))
      (fun t _ => (taylor_deriv M t).continuousAt.continuousWithinAt)
      (fun t _ => (taylor_deriv M t).hasDerivWithinAt)
      (B := fun s => s ^ (M + 1) / ((M + 1).factorial : ℝ)) (B' := fun t => t ^ M / (M.factorial : ℝ))
      (by simp [Finset.sum_range_succ']) hB
      (fun t ht => by
        rw [norm_mul, Complex.norm_I, one_mul]
        exact ih t ht.1)
      (Set.right_mem_Icc.mpr hx)
    simpa using this

/-- The sharp Taylor bound for `exp(ix)`, every real `x`: `|e^{ix} - ∑_{m<M} (ix)^m/m!| ≤ |x|^M/M!`. -/
private lemma taylor_all (x : ℝ) (M : ℕ) :
    ‖Complex.exp ((x : ℂ) * Complex.I)
      - ∑ m ∈ Finset.range M, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖
      ≤ |x| ^ M / M.factorial := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact taylor_nonneg M x hx
  · have h := taylor_nonneg M (-x) (by linarith)
    rw [abs_of_nonpos hx]
    have hc : Complex.exp ((x : ℂ) * Complex.I)
        - ∑ m ∈ Finset.range M, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
        = (starRingEnd ℂ) (Complex.exp (((-x : ℝ) : ℂ) * Complex.I)
          - ∑ m ∈ Finset.range M, (((-x : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) := by
      have hz : (starRingEnd ℂ) (((-x : ℝ) : ℂ) * Complex.I) = (x : ℂ) * Complex.I := by
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
      rw [map_sub, map_sum, ← Complex.exp_conj, hz]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_div₀, map_pow, hz, map_natCast]
    rw [hc, Complex.norm_conj]
    exact h

/-- `ω(u) = #{p ≤ B prime : p ∣ u}` for `0 < u ≤ B`. -/
private lemma omega_eq_sum_primes_le {u B : ℕ} (hu : 0 < u) (huB : u ≤ B) :
    (ArithmeticFunction.cardDistinctFactors u : ℝ)
      = ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime, (if p ∣ u then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole, omega_eq_card_pf]
  congr 2
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hd, -⟩
    have := Nat.le_of_dvd hu hd
    exact ⟨⟨by omega, hp⟩, hd⟩
  · rintro ⟨⟨-, hp⟩, hd⟩
    exact ⟨hp, hd, hu.ne'⟩

/-- (5.12)–(5.13): the truncated phase is `∑_p X_p`, the sum over the primes up to `B`. -/
private lemma phase_split {β : Type*} [Fintype β] (q : ℝ) (H B : ℕ) (c : β → ℝ) (d : ℕ → ℝ)
    (u : ℕ → β → ℕ) (hu : ∀ k < H, ∀ b, 0 < u k b ∧ u k b ≤ B) :
    q * ∑ k ∈ Finset.range H, (∑ b, c b * (ArithmeticFunction.cardDistinctFactors (u k b) : ℝ)) / d k
      = ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime,
          q * ∑ k ∈ Finset.range H, (∑ b, c b * (if p ∣ u k b then (1 : ℝ) else 0)) / d k := by
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := hu k (Finset.mem_range.mp hk) b
  rw [← Finset.mul_sum, ← omega_eq_sum_primes_le h.1 h.2]

private lemma avg_abs_add3 {ι : Type*} (s : Finset ι) (a b c : ι → ℝ) :
    (s.card : ℝ)⁻¹ * ∑ i ∈ s, |a i + b i + c i|
      ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, |a i| + (s.card : ℝ)⁻¹ * ∑ i ∈ s, |b i|
        + (s.card : ℝ)⁻¹ * ∑ i ∈ s, |c i| := by
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => abs_add_three _ _ _)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- `E|f| ≤ (E f²)^{1/2}` (Cauchy–Schwarz), used for `κ₃` as defined in (5.14). -/
private lemma avg_abs_le_sqrt {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (s.card : ℝ)⁻¹ * ∑ i ∈ s, |f i| ≤ Real.sqrt ((s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ 2) := by
  have h0 : 0 ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, |f i| :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  rw [← Real.sqrt_sq h0]
  apply Real.sqrt_le_sqrt
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => |f i|)
  simp only [sq_abs] at hcs
  rcases Nat.eq_zero_or_pos s.card with h | h
  · simp [h]
  · have hN : (0 : ℝ) < s.card := by exact_mod_cast h
    rw [mul_pow, inv_pow]
    calc ((s.card : ℝ) ^ 2)⁻¹ * (∑ i ∈ s, |f i|) ^ 2
        ≤ ((s.card : ℝ) ^ 2)⁻¹ * ((s.card : ℝ) * ∑ i ∈ s, f i ^ 2) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hcs) (by positivity)
      _ = (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ 2 := by field_simp

/-- `|(-1)^{|ε|}| = 1`. -/
private lemma abs_sgn_le_one {K : ℕ} (ε : Fin K → Bool) :
    |∏ i, (if ε i then (-1 : ℝ) else 1)| ≤ 1 := by
  rw [Finset.abs_prod]
  refine le_of_eq (Finset.prod_eq_one fun i _ => ?_)
  split_ifs <;> simp

/-- `|q ∑_ε (-1)^{|ε|} ∑_k g| ≤ q ∑_ε ∑_k g` for `g ≥ 0`: the `δ_p` terms of (5.8) against `κ₁`. -/
private lemma abs_sgn_tsum_le {K : ℕ} (q : ℝ) (hq : 0 ≤ q) (sgn : (Fin K → Bool) → ℝ)
    (hsgn : ∀ ε, |sgn ε| ≤ 1) (g : (Fin K → Bool) → ℕ → ℝ) (hg : ∀ ε k, 0 ≤ g ε k) :
    |q * ∑ ε, sgn ε * ∑' k, g ε k| ≤ q * ∑ ε, ∑' k, g ε k := by
  rw [abs_mul, abs_of_nonneg hq]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun ε _ => ?_)) hq
  rw [abs_mul, abs_of_nonneg (tsum_nonneg (hg ε))]
  exact mul_le_of_le_one_left (tsum_nonneg (hg ε)) (hsgn ε)

/-- Truncation (5.11): `|∑ T - ∑_{k<H} T| ≤ ∑_{k} G(k+H)` when `|T| ≤ G` and `G` is summable. -/
private lemma tail_abs_le (T G : ℕ → ℝ) (hT : ∀ k, |T k| ≤ G k) (hG : Summable G) (H : ℕ) :
    |∑' k, T k - ∑ k ∈ Finset.range H, T k| ≤ ∑' k, G (k + H) := by
  have hTs : Summable T :=
    Summable.of_norm_bounded hG (fun k => by rw [Real.norm_eq_abs]; exact hT k)
  rw [← hTs.sum_add_tsum_nat_add H, add_sub_cancel_left]
  have hTH : Summable fun k => T (k + H) := (summable_nat_add_iff H).mpr hTs
  have hGH : Summable fun k => G (k + H) := (summable_nat_add_iff H).mpr hG
  rw [abs_le]
  constructor
  · rw [← tsum_neg]
    exact Summable.tsum_le_tsum (fun k => neg_le_of_abs_le (hT (k + H))) hGH.neg hTH
  · exact Summable.tsum_le_tsum (fun k => le_of_abs_le (hT (k + H))) hTH hGH

private lemma abs_sgn_sum_div_le {β : Type*} [Fintype β] (sgn : β → ℝ) (hs : ∀ b, |sgn b| ≤ 1)
    (w : β → ℝ) (hw : ∀ b, 0 ≤ w b) (d : ℝ) (hd : 0 < d) :
    |(∑ b, sgn b * w b) / d| ≤ (∑ b, w b) / d := by
  rw [abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun b _ => by
      rw [abs_mul, abs_of_nonneg (hw b)]; exact mul_le_of_le_one_left (hw b) (hs b))) hd.le

/-- Erdős 257 for `A` the set of primes: `∑_p 1/(2^p - 1) = ∑_{n ≥ 1} ω(n)/2^n` is irrational
(this is also Erdős problem 69). Known: T. Tao and J. Teräväinen, *Quantitative correlations and
some problems on prime factors of consecutive integers*, arXiv:2512.01739 (v2, 2026), Theorem 1.3
(§1.3); earlier conditional on a uniform prime tuples conjecture (Pratt 2024). The paper only
sketches the analogous case of the prime powers ("we leave the details … to the interested
reader"), so that case is not stated here. -/
theorem Opn.erdos_257_primes :
    Irrational (∑' p : {p : ℕ | p.Prime}, (1 : ℝ) / (2 ^ p.1 - 1)) := by
  -- approach: Tao–Teräväinen §5: rationality forces (5.8) on every prime cube; averaging e(phase) over n and the variance bound (5.20) contradict Theorem 5.1
  -- licence: CC-BY-4.0
  -- label: Tao–Teräväinen Theorem 5.1 (technical reduction)
  -- claim: $\forall q \ge 1\ \exists c_0 > 0\ \forall \delta > 0:\ \text{a prime cube } p_\varepsilon = p_0 + \textstyle\sum_k \varepsilon_k v_k,
  -- \text{ a finite set of } n \text{ obeying (5.5)--(5.6), a split } S_0 \sqcup S_1 \sqcup S_2 \text{ of the primes} \le B
  -- \text{ with } X_p \text{ constant on } S_0,\ |X_p| \le \delta \text{ on } S_1,\ M \text{ even},\ \kappa_1, \dots, \kappa_5 \le \delta,\ \sum_{p \in S_1} \operatorname{Var} X_p \ge c_0$
  -- Theorem 5.1 of arXiv:2512.01739v2 (p. 49) for n uniform on the finite set Ns, where
  -- X_p(n) = q sum_{1<=h<=H} sum_eps (-1)^|eps| 1[p | n + r_{eps,h+K}] / 2^(h+K) is (5.13), and
  -- kappa_1, kappa_2, kappa_3 are (5.10), (5.11), (5.14) as printed (expectation and sums swapped).
  -- kappa_4, kappa_5 are (5.16), (5.17) as printed, with X'_p independent copies (n uniform on
  -- Ns^{S_1}) and e = exp 1 in (5.17). One part is taken from the paper's proof rather than its
  -- statement: (5.19), |X_p| small on S_1 (shown in section 5.6 from (5.36)). It does not mention the sum or
  -- rationality: it is about prime factors of shifted integers, and in the paper its proof rests on
  -- the paper's Theorem 3.1 and on Lemma 5.2.
  have h1 : ∀ q : ℕ, 0 < q → ∃ c0 : ℝ, 0 < c0 ∧ ∀ δ : ℝ, 0 < δ →
      ∃ (K : ℕ) (p0 : ℤ) (v : Fin K → ℤ) (P : (Fin K → Bool) → ℕ) (H B : ℕ) (Ns : Finset ℤ)
        (m : ℤ → (Fin K → Bool) → ℕ) (S1 S2 : Finset ℕ) (sgn : (Fin K → Bool) → ℝ)
        (r : (Fin K → Bool) → ℕ → ℤ) (X : ℕ → ℤ → ℝ) (M : ℕ),
        (∀ ε, sgn ε = ∏ i, if ε i then (-1 : ℝ) else 1) ∧
        (∀ ε (h : ℕ), r ε h = p0 * h + ∑ k : Fin K, ((h : ℤ) - (k.1 + 1)) * (if ε k then v k else 0)) ∧
        (∀ p n, X p n = (q : ℝ) * ∑ k ∈ Finset.range H, (∑ ε : Fin K → Bool, sgn ε *
            (if p ∣ (n + r ε (k + K + 1)).toNat then (1 : ℝ) else 0)) / 2 ^ (k + K + 1)) ∧
        Even M ∧
        (∀ ε, (P ε : ℤ) = p0 + ∑ k : Fin K, (if ε k then v k else 0)) ∧ (∀ ε, (P ε).Prime) ∧
        Ns.Nonempty ∧
        (∀ n ∈ Ns, ∀ ε, n - ∑ k : Fin K, ((k.1 : ℤ) + 1) * (if ε k then v k else 0) = P ε * m n ε) ∧
        (∀ n ∈ Ns, ∀ ε, ∀ k < H, 0 < n + r ε (k + K + 1) ∧ n + r ε (k + K + 1) ≤ B) ∧
        S1 ⊆ (Finset.range (B + 1)).filter Nat.Prime ∧ S2 ⊆ (Finset.range (B + 1)).filter Nat.Prime ∧
        Disjoint S1 S2 ∧
        (∀ p ∈ (Finset.range (B + 1)).filter Nat.Prime, p ∉ S1 → p ∉ S2 →
          ∀ n ∈ Ns, ∀ n' ∈ Ns, X p n = X p n') ∧
        (∀ p ∈ S1, ∀ n ∈ Ns, |X p n| ≤ δ) ∧
        (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, ∑ ε : Fin K → Bool, ∑' k : ℕ,
            (if P ε ^ 2 ∣ P ε * m n ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) ≤ δ ∧
        (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, ∑' k : ℕ, (∑ ε : Fin K → Bool,
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + H + K + 1)).toNat : ℝ))
            / 2 ^ (k + H + K + 1) ≤ δ ∧
        Real.sqrt ((Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (∑ p ∈ S2, X p n) ^ 2) ≤ δ ∧
        ∑ j ∈ Finset.range (M + 1), (2 * Real.pi) ^ j / j.factorial
          * |(Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (∑ p ∈ S1, X p n) ^ j
            - ((Fintype.piFinset (fun _ : S1 => Ns)).card : ℝ)⁻¹
              * ∑ ω ∈ Fintype.piFinset (fun _ : S1 => Ns), (∑ p : S1, X p (ω p)) ^ j| ≤ δ ∧
        (∏ p ∈ S1, (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, Real.exp (2 * Real.pi * Real.exp 1 * X p n)
            + ∏ p ∈ S1, (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns,
              Real.exp (-(2 * Real.pi * Real.exp 1) * X p n)) / Real.exp 1 ^ M ≤ δ ∧
        c0 ≤ ∑ p ∈ S1, ((Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, X p n ^ 2
          - ((Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, X p n) ^ 2) := sorry
  have htay := taylor_all
  rintro ⟨r0, hr0⟩
  have hq : 0 < r0.den := r0.den_pos
  have hsum : ∑' p : {p : ℕ | p.Prime}, (1 : ℝ) / (2 ^ p.1 - 1) = (r0.num : ℝ) / (r0.den : ℕ) := by
    rw [← hr0, Rat.cast_def]
  obtain ⟨c0, hc0, hall⟩ := h1 r0.den hq
  have hex : Real.exp (-8 * c0) < 1 := by
    have := Real.exp_lt_exp.mpr (show -8 * c0 < 0 by linarith)
    rwa [Real.exp_zero] at this
  have hδ : 0 < min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) := lt_min (by norm_num) (by linarith)
  have hδ1 : min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) ≤ 1 / 4 := min_le_left _ _
  have hδ2 : min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) ≤ (1 - Real.exp (-8 * c0)) / 64 :=
    min_le_right _ _
  obtain ⟨K, p0, v, P, H, B, Ns, m, S1, S2, sgn, r, X, M, hsgn, hr, hX, hMeven, hP, hpr, hNs, hm, hrange,
    hS1, hS2, hdisj, hS0, hXs, hk1, hk2, hk3, hk4, hk5, hvar⟩ :=
    hall (min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) / r0.den) (div_pos hδ (by positivity))
  have hq1 : (1 : ℝ) ≤ r0.den := by exact_mod_cast hq
  have hd1 : min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) / r0.den
      ≤ min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) := div_le_self hδ.le hq1
  have hd2 : (r0.den : ℝ) * (min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) / r0.den)
      = min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) :=
    mul_div_cancel₀ _ (by positivity)
  have hsgn' : cubeSgn = sgn := funext fun ε => by rw [hsgn ε]; rfl
  have hr' : cubeShift p0 v = r := funext fun ε => funext fun h => by rw [hr ε h]; rfl
  obtain ⟨n0, hn0⟩ := hNs
  have key := assembly_core Ns ⟨n0, hn0⟩ S1 X
    (fun n => (r0.den : ℝ) * ∑ ε : Fin K → Bool, sgn ε * ∑' k : ℕ,
            (if P ε ^ 2 ∣ P ε * m n ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)
      + ((r0.den : ℝ) * ∑' k : ℕ, (∑ ε : Fin K → Bool, sgn ε *
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + K + 1)).toNat : ℝ)) / 2 ^ (k + K + 1)
          - (r0.den : ℝ) * ∑ k ∈ Finset.range H, (∑ ε : Fin K → Bool, sgn ε *
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + K + 1)).toNat : ℝ)) / 2 ^ (k + K + 1))
      + ∑ p ∈ S2, X p n)
    (∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime \ (S1 ∪ S2), X p n0)
    (4 * min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64)) c0 ?_
    (fun p hp n hn => ((hXs p hp n hn).trans hd1).trans hδ1) ?_ ((decor_bound Ns S1 X M hMeven htay).trans (by linarith)) hvar
  · linarith
  · intro n hn
    obtain ⟨z, hz⟩ := rational_imp_5_8 r0.num r0.den hq hsum p0 v P hP hpr n (m n) (hm n hn)
    rw [hsgn', hr'] at hz
    refine ⟨z, ?_⟩
    have hu : ∀ k < H, ∀ ε : Fin K → Bool,
        0 < (n + r ε (k + K + 1)).toNat ∧ (n + r ε (k + K + 1)).toNat ≤ B := by
      intro k hk ε
      have h := hrange n hn ε k hk
      constructor <;> omega
    have hsplit := phase_split (r0.den : ℝ) H B sgn (fun k => (2 : ℝ) ^ (k + K + 1))
      (fun k ε => (n + r ε (k + K + 1)).toNat) hu
    beta_reduce at hsplit
    have hPB : ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime, X p n
        = ∑ p ∈ S1, X p n + ∑ p ∈ S2, X p n
          + ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime \ (S1 ∪ S2), X p n := by
      rw [← Finset.sum_union hdisj]
      exact (Finset.sum_sdiff (Finset.union_subset hS1 hS2)).symm.trans (add_comm _ _)
    have hC : ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime \ (S1 ∪ S2), X p n
        = ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime \ (S1 ∪ S2), X p n0 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Finset.mem_sdiff.mp hp
      exact hS0 p hp'.1 (fun h => hp'.2 (Finset.mem_union_left _ h))
        (fun h => hp'.2 (Finset.mem_union_right _ h)) n hn n0 hn0
    have hXsum : ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime,
        (r0.den : ℝ) * ∑ k ∈ Finset.range H, (∑ ε : Fin K → Bool, sgn ε *
            (if p ∣ (n + r ε (k + K + 1)).toNat then (1 : ℝ) else 0)) / 2 ^ (k + K + 1)
        = ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime, X p n :=
      Finset.sum_congr rfl fun p _ => (hX p n).symm
    linarith
  · refine (avg_abs_add3 Ns _ _ _).trans ?_
    have e1 : (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, |(r0.den : ℝ) * ∑ ε : Fin K → Bool, sgn ε * ∑' k : ℕ,
            (if P ε ^ 2 ∣ P ε * m n ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)|
        ≤ min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) := by
      have hs1 : ∀ ε, |sgn ε| ≤ 1 := fun ε => by rw [hsgn ε]; exact abs_sgn_le_one ε
      calc (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, |(r0.den : ℝ) * ∑ ε : Fin K → Bool, sgn ε * ∑' k : ℕ,
            (if P ε ^ 2 ∣ P ε * m n ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)|
          ≤ (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (r0.den : ℝ) * ∑ ε : Fin K → Bool, ∑' k : ℕ,
            (if P ε ^ 2 ∣ P ε * m n ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ =>
              abs_sgn_tsum_le _ (Nat.cast_nonneg _) sgn hs1 _ fun ε k =>
                div_nonneg (by split_ifs <;> norm_num) (by positivity))
              (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = (r0.den : ℝ) * ((Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, ∑ ε : Fin K → Bool, ∑' k : ℕ,
            (if P ε ^ 2 ∣ P ε * m n ε + P ε * (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)) := by
            rw [← Finset.mul_sum]; ring
        _ ≤ (r0.den : ℝ) * (min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) / r0.den) :=
            mul_le_mul_of_nonneg_left hk1 (Nat.cast_nonneg _)
        _ = min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) := hd2
    have hs1 : ∀ ε, |sgn ε| ≤ 1 := fun ε => by rw [hsgn ε]; exact abs_sgn_le_one ε
    have e2 : (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, |(r0.den : ℝ) * ∑' k : ℕ, (∑ ε : Fin K → Bool, sgn ε *
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + K + 1)).toNat : ℝ)) / 2 ^ (k + K + 1)
          - (r0.den : ℝ) * ∑ k ∈ Finset.range H, (∑ ε : Fin K → Bool, sgn ε *
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + K + 1)).toNat : ℝ)) / 2 ^ (k + K + 1)|
        ≤ min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) := by
      have hper : ∀ n ∈ Ns, |(r0.den : ℝ) * ∑' k : ℕ, (∑ ε : Fin K → Bool, sgn ε *
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + K + 1)).toNat : ℝ)) / 2 ^ (k + K + 1)
          - (r0.den : ℝ) * ∑ k ∈ Finset.range H, (∑ ε : Fin K → Bool, sgn ε *
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + K + 1)).toNat : ℝ)) / 2 ^ (k + K + 1)|
          ≤ (r0.den : ℝ) * ∑' k : ℕ, (∑ ε : Fin K → Bool,
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + H + K + 1)).toNat : ℝ))
            / 2 ^ (k + H + K + 1) := by
        intro n hn
        have hsh : ∀ ε (h : ℕ), (n + r ε h).toNat = P ε * m n ε + P ε * h := by
          intro ε h
          have : n + r ε h = ((P ε * m n ε + P ε * h : ℕ) : ℤ) := by
            rw [← hr', cubeShift_eq, ← hP ε]; push_cast; linear_combination hm n hn ε
          rw [this, Int.toNat_natCast]
        have hG : Summable fun k : ℕ => (∑ ε : Fin K → Bool,
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + K + 1)).toNat : ℝ))
            / 2 ^ (k + K + 1) := by
          simp_rw [Finset.sum_div]
          refine summable_sum fun ε _ => ?_
          have hb := omega_bound_summable (fun k => P ε * m n ε + P ε * (k + K + 1))
            (P ε * m n ε + P ε * (K + 1)) (P ε) (fun k => le_of_eq (by ring))
          refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hb
          rw [hsh ε]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_right₀ (by norm_num) (by omega))
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (tail_abs_le _ _ (fun k => abs_sgn_sum_div_le sgn hs1 _
          (fun ε => Nat.cast_nonneg _) _ (by positivity)) hG H) (Nat.cast_nonneg _)
      calc _ ≤ (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, (r0.den : ℝ) * ∑' k : ℕ, (∑ ε : Fin K → Bool,
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + H + K + 1)).toNat : ℝ))
            / 2 ^ (k + H + K + 1) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = (r0.den : ℝ) * ((Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, ∑' k : ℕ, (∑ ε : Fin K → Bool,
            (ArithmeticFunction.cardDistinctFactors (n + r ε (k + H + K + 1)).toNat : ℝ))
            / 2 ^ (k + H + K + 1)) := by rw [← Finset.mul_sum]; ring
        _ ≤ (r0.den : ℝ) * (min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) / r0.den) :=
            mul_le_mul_of_nonneg_left hk2 (Nat.cast_nonneg _)
        _ = min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) := hd2
    have e3 : (Ns.card : ℝ)⁻¹ * ∑ n ∈ Ns, |∑ p ∈ S2, X p n|
        ≤ min (1 / 4 : ℝ) ((1 - Real.exp (-8 * c0)) / 64) :=
      ((avg_abs_le_sqrt Ns fun n => ∑ p ∈ S2, X p n).trans hk3).trans hd1
    linarith
