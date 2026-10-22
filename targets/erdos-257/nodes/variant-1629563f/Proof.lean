import Mathlib
import Nodes.«variant-1629563f».Context

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

/-- Liouville's criterion for Erdős 257: let `A` be an infinite set of positive integers such
that, for every `C`, some `m ∈ A` has a common multiple `L` of the numbers `2^a - 1` over the
elements `a < m` of `A` with `2^C · L ≤ 2^m` (the elements below `m` have a small common
denominator compared with the gap the tail leaves). Then `∑_{n ∈ A} 1/(2^n - 1)` is irrational.
Proof: if the sum were `p/q`, take `C` with `2^C > 4q`; with `L` as above, `q · L` times the tail
from `m` on is a positive integer, but the tail is below `4 · 2^(-m)`, so it is below
`4q · 2^(-C) < 1`. The criterion covers every set that is eventually lacunary of ratio two
(`Opn.erdos_257_eventually_ratio_two`: `{2^k}`, `{2^k - 1}`, `{3^k}`, `{k!}`, divisibility
chains). It does not reach sets of positive density, nor lacunary sets of ratio below two in
general; those need Erdős's arguments (1948, 1968). -/
theorem Opn.erdos_257_liouville_criterion :
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
