import Mathlib
import Nodes.«variant-09e95e7a».Context

/-! A related variant of Erdős problem 69 (D-30, relation `related`): the binary number whose
n-th digit is 1 exactly when n is prime, `∑_{p prime} 2^{-p}`, is irrational.

Why it sits beside erdos-69: the root's standing decomposition (erdos-69--h2-v2 and below) turns
rationality of `∑ ω(n)/2^n` into "b times every tail `∑_{j≥1} ω(N+j)/2^j` is an integer" and is
blocked on controlling ω on a window of consecutive integers. For the prime indicator the same
tail argument closes, because the window is controllable: `(k+1)! + 2, …, (k+1)! + k + 1` are
all composite, so the tail after `N = (k+1)! + 1` lies strictly between 0 and `2^{-k}`. This
node is a worked, gate-checked instance of the method, not progress on the root. -/

theorem Opn.erdos_69_prime_indicator :
    Irrational (∑' n : ℕ, if n.Prime then (1 / 2 : ℝ) ^ n else 0) := by
  set f : ℕ → ℝ := fun n => if n.Prime then (1 / 2 : ℝ) ^ n else 0 with hf
  have f_nonneg : ∀ n, 0 ≤ f n := fun n => by
    simp only [hf]; split_ifs <;> positivity
  have f_le : ∀ n, f n ≤ (1 / 2 : ℝ) ^ n := fun n => by
    simp only [hf]; split_ifs
    · exact le_rfl
    · positivity
  have hs : Summable f :=
    Summable.of_nonneg_of_le f_nonneg f_le
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  rintro ⟨q, hq⟩
  set k := q.den with hk
  have kpos : 0 < k := q.den_pos
  set N := (k + 1).factorial + 1 with hN
  -- the k integers after N are composite
  have comp : ∀ j, j < k → f (j + k * 0 + (N + 1)) = 0 := by
    intro j hj
    simp only [hf, mul_zero, add_zero]
    rw [if_neg]
    intro hp
    have hd : (j + 2) ∣ j + (N + 1) := by
      have : (j + 2) ∣ (k + 1).factorial := Nat.dvd_factorial (by omega) (by omega)
      have e : j + (N + 1) = (k + 1).factorial + (j + 2) := by rw [hN]; ring
      rw [e]; exact dvd_add this dvd_rfl
    rcases hp.eq_one_or_self_of_dvd _ hd with h | h
    · omega
    · have : 0 < (k + 1).factorial := Nat.factorial_pos _
      rw [hN] at h; omega
  have hg : Summable (fun i => f (i + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr hs
  have hg' : Summable (fun i => f (i + k + (N + 1))) := by
    have := (summable_nat_add_iff k).mpr hg
    simpa [add_assoc] using this
  have split1 := Summable.sum_add_tsum_nat_add (N + 1) hs
  have split2 := Summable.sum_add_tsum_nat_add k hg
  have zero_part : ∑ i ∈ Finset.range k, f (i + (N + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have := comp j (Finset.mem_range.mp hj)
    simpa using this
  set R := ∑' i, f (i + k + (N + 1)) with hR
  have split2' : ∑' i, f (i + (N + 1)) = R := by
    rw [← split2, zero_part, zero_add]
  -- R is positive
  have Rpos : 0 < R := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (k + (N + 1))
    have hpi : p - (k + (N + 1)) + k + (N + 1) = p := by omega
    refine hg'.tsum_pos (fun i => f_nonneg _) (p - (k + (N + 1))) ?_
    rw [hpi]; simp only [hf, if_pos hp2]; positivity
  -- R is small
  have geo : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + k + (N + 1))) := by
    have := (summable_nat_add_iff (k + (N + 1))).mpr
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num))
    simpa [add_assoc] using this
  have Rle : R ≤ (1 / 2 : ℝ) ^ (k + (N + 1)) * 2 := by
    calc R ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + k + (N + 1)) :=
          Summable.tsum_le_tsum (fun i => f_le _) hg' geo
      _ = (1 / 2 : ℝ) ^ (k + (N + 1)) * 2 := by
          simp_rw [add_assoc, pow_add]
          rw [tsum_mul_right, tsum_geometric_two, mul_comm]
  have key : (2 : ℝ) ^ N * ((1 / 2 : ℝ) ^ (k + (N + 1)) * 2) = (1 / 2) ^ k := by
    have h1 : (2 : ℝ) ^ N * (1 / 2) ^ N = 1 := by rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ N * ((1 / 2 : ℝ) ^ (k + (N + 1)) * 2)
        = (1 / 2) ^ k * ((2 : ℝ) ^ N * (1 / 2) ^ N) * ((1 / 2) * 2) := by
          rw [pow_add, pow_succ]; ring
      _ = (1 / 2) ^ k := by rw [h1]; norm_num
  -- the finite part times 2^N is an integer
  set Z : ℕ := ∑ i ∈ Finset.range (N + 1), if i.Prime then 2 ^ (N - i) else 0 with hZ
  have hZ' : (2 : ℝ) ^ N * ∑ i ∈ Finset.range (N + 1), f i = (Z : ℝ) := by
    rw [hZ, Finset.mul_sum]; push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [hf]
    split_ifs
    · have e : (2 : ℝ) ^ N = 2 ^ (N - i) * 2 ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hi']
      rw [e, mul_assoc, ← mul_pow]; norm_num
    · simp
  have hqk : (q : ℝ) * k = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  -- m := k * 2^N * R is an integer
  have hx : (q : ℝ) = ∑ i ∈ Finset.range (N + 1), f i + R := by
    rw [hq, ← split1, split2']
  have hm : ((2 ^ N * q.num - k * Z : ℤ) : ℝ) = (k : ℝ) * ((2 : ℝ) ^ N * R) := by
    push_cast
    rw [← hqk, hx, ← hZ']; ring
  have mpos : (0 : ℝ) < ((2 ^ N * q.num - k * Z : ℤ) : ℝ) := by
    rw [hm]; have : (0 : ℝ) < k := by exact_mod_cast kpos
    positivity
  have mlt : ((2 ^ N * q.num - k * Z : ℤ) : ℝ) < 1 := by
    rw [hm]
    have h2 : (2 : ℝ) ^ N * R ≤ (1 / 2) ^ k := by
      rw [← key]; exact mul_le_mul_of_nonneg_left Rle (by positivity)
    have hk2 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have hk0 : (0 : ℝ) ≤ k := by positivity
    calc (k : ℝ) * ((2 : ℝ) ^ N * R) ≤ k * (1 / 2) ^ k := mul_le_mul_of_nonneg_left h2 hk0
      _ = k / 2 ^ k := by rw [one_div_pow, mul_one_div]
      _ < 1 := by rw [div_lt_one (by positivity)]; exact hk2
  have i1 : (0 : ℤ) < 2 ^ N * q.num - k * Z := by exact_mod_cast mpos
  have i2 : 2 ^ N * q.num - k * Z < (1 : ℤ) := by exact_mod_cast mlt
  omega
