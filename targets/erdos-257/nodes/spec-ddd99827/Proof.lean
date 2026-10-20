import Mathlib
import Nodes.«spec-ddd99827».Context

/-- Each term of the Mersenne reciprocal series exceeds the sum of all later terms:
`∑_{m > n} 1/(2^m - 1) < 1/(2^n - 1)` for `n ≥ 1`. This is the gap condition that makes the
subset sums `∑_{a ∈ A} 1/(2^a - 1)` a Cantor set in which every point has exactly one
representation (Kovač–Tao, arXiv:2406.17593, Remark 4.1); every greedy or counting attack on
Erdős 257 rests on it. -/
theorem Opn.erdos_257_tail_lt_term (n : ℕ) (hn : 1 ≤ n) :
    ∑' k : ℕ, (1 : ℝ) / (2 ^ (n + 1 + k) - 1) < 1 / (2 ^ n - 1) := by
  have h2n : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hpos1 : (0 : ℝ) < 2 ^ (n + 1) - 1 := by
    rw [pow_succ]; linarith
  -- each term is at most (1/(2^(n+1)-1)) * (1/2)^k
  have hterm : ∀ k : ℕ, (1 : ℝ) / (2 ^ (n + 1 + k) - 1) ≤ (1 / (2 ^ (n + 1) - 1)) * (1 / 2) ^ k := by
    intro k
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hpow : (2 : ℝ) ^ (n + 1 + k) = 2 ^ (n + 1) * 2 ^ k := by rw [pow_add]
    have hposk : (0 : ℝ) < 2 ^ (n + 1 + k) - 1 := by
      rw [hpow]; nlinarith
    rw [one_div_pow, div_mul_div_comm, one_mul, div_le_div_iff₀ hposk (by positivity), hpow]
    nlinarith
  have hnonneg : ∀ k : ℕ, (0 : ℝ) ≤ 1 / (2 ^ (n + 1 + k) - 1) := by
    intro k
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hpow : (2 : ℝ) ^ (n + 1 + k) = 2 ^ (n + 1) * 2 ^ k := by rw [pow_add]
    have hposk : (0 : ℝ) < 2 ^ (n + 1 + k) - 1 := by
      rw [hpow]; nlinarith
    exact div_nonneg zero_le_one hposk.le
  have hsum : Summable (fun k : ℕ => (1 / ((2 : ℝ) ^ (n + 1) - 1)) * (1 / 2) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∑' k : ℕ, (1 : ℝ) / (2 ^ (n + 1 + k) - 1)
      ≤ ∑' k : ℕ, (1 / ((2 : ℝ) ^ (n + 1) - 1)) * (1 / 2) ^ k :=
    Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le hnonneg hterm hsum) hsum
  have hgeom : ∑' k : ℕ, (1 / ((2 : ℝ) ^ (n + 1) - 1)) * (1 / 2) ^ k = 2 / (2 ^ (n + 1) - 1) := by
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  calc ∑' k : ℕ, (1 : ℝ) / (2 ^ (n + 1 + k) - 1) ≤ 2 / (2 ^ (n + 1) - 1) := hgeom ▸ hle
    _ < 1 / (2 ^ n - 1) := by
      rw [div_lt_div_iff₀ hpos1 (by linarith), pow_succ]
      linarith
