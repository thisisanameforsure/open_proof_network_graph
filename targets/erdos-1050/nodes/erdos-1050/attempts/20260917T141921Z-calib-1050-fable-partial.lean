/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-! Erdős problem 1050 (calibration): a known result — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1050.lean at c7f31d5fd3d2ca3d69979f2d213eb9b58fe956ae, Apache-2.0); as stated. A calibration target (Stages v3.17, F15-R14): a known result, drafted by docs/calibration_pool.py and read by the curator before intake. -/

theorem Opn.erdos_1050 :
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
  -- annex: ebfc846b7b9ca01cf3880bbde14e6a4909e741934a08f0b4d43f8aa3b2405cb2
  -- Borwein's theorem for the tail T = ∑_{n ≥ 3} 1/(2^n − 3), in Diophantine-approximant form:
  -- integer sequences a, b with b n * T − a n never zero and tending to zero (Borwein 1991, 1992).
  have borwein : ∃ a b : ℕ → ℤ,
      (∀ n : ℕ, (b n : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3)) - a n ≠ 0) ∧
      Filter.Tendsto
        (fun n : ℕ => (b n : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3)) - a n)
        Filter.atTop (nhds 0) := by
    sorry
  -- The irrationality criterion: a real with such approximants is irrational.
  have criterion : ∀ x : ℝ, (∃ a b : ℕ → ℤ, (∀ n : ℕ, (b n : ℝ) * x - a n ≠ 0) ∧
      Filter.Tendsto (fun n : ℕ => (b n : ℝ) * x - a n) Filter.atTop (nhds 0)) →
      Irrational x := by
    rintro x ⟨a, b, hne, hlim⟩ ⟨r, hr⟩
    subst hr
    have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) (1 / r.den) (by positivity)
    have h := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at h
    have hnum : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
    have key : ((b N : ℝ) * r - a N) * r.den = ((b N * r.num - a N * r.den : ℤ) : ℝ) := by
      push_cast
      linear_combination (b N : ℝ) * hnum
    have hz : (b N * r.num - a N * r.den : ℤ) ≠ 0 := by
      intro h0
      have h1 := key
      rw [h0] at h1
      push_cast at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hne N h2
      · exact absurd h2 hden.ne'
    have hge : (1 : ℝ) ≤ |((b N * r.num - a N * r.den : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hz
    rw [← key, abs_mul, abs_of_pos hden] at hge
    have hlt : |(b N : ℝ) * r - a N| * r.den < 1 / r.den * r.den :=
      mul_lt_mul_of_pos_right h hden
    rw [one_div_mul_cancel hden.ne'] at hlt
    linarith
  have hT : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3)) := criterion _ borwein
  -- The literal series is the tail: its first two terms are −1 and 1.
  have hpos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ (n + 3) - 3 := by
    intro n
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have : (2 : ℝ) ^ (n + 3) = 8 * 2 ^ n := by ring
    rw [this]
    linarith
  have htail : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + 1) - 3)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    · exact div_nonneg zero_le_one (hpos n).le
    · rw [one_div_pow]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have : (2 : ℝ) ^ (n + 2 + 1) = 8 * 2 ^ n := by ring
      rw [this]
      linarith
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) :=
    (summable_nat_add_iff 2).mp htail
  have hre : (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) =
      ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3) := by
    rw [← hsum.sum_add_tsum_nat_add 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [hre]
  exact hT
