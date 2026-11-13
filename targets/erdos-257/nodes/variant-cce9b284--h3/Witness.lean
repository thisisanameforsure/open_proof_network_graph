import Mathlib
import Nodes.«variant-cce9b284--h3».Context

theorem witness : ∃ (L : ℕ) (p : ℕ) (r : ℕ → ℝ) (n : ℕ) (m : ℕ),
  r (0 : ℕ) = (↑p : ℝ) / (2 : ℝ) ^ L ∧
    (∀ (k : ℕ),
        r (k + (1 : ℕ)) =
          if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ))
          else r k) ∧
      L ≤ n ∧
        n < m ∧
          m + (10 : ℕ) ≤ (2 : ℕ) * n ∧
            r (n + (1 : ℕ)) < (1 : ℝ) / ((2 : ℝ) ^ (n + (1 : ℕ)) - (1 : ℝ)) ∧
              ∑' (i : ℕ), (1 : ℝ) / ((2 : ℝ) ^ (n + (2 : ℕ) + i) - (1 : ℝ)) < r (n + (1 : ℕ)) := by
  classical
  -- the greedy walk of 17891 / 2^15, which stalls at step 16
  let r : ℕ → ℝ := fun n => Nat.rec (motive := fun _ => ℝ) ((17891 : ℝ) / 32768)
    (fun (k : ℕ) (acc : ℝ) => if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ acc
      then acc - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) else acc) n
  have hr : ∀ (k : ℕ), r (k + (1 : ℕ)) =
      if (1 : ℕ) ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ)) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - (1 : ℝ))
      else r k := fun k => rfl
  have h0 : r 0 = (17891 : ℝ) / 32768 := rfl
  have h1 : r 1 = (17891 : ℝ) / 32768 := by
    show r (0 + 1) = (17891 : ℝ) / 32768
    rw [hr 0, h0]
    norm_num
  have h2 : r 2 = (17891 : ℝ) / 32768 := by
    show r (1 + 1) = (17891 : ℝ) / 32768
    rw [hr 1, h1]
    norm_num
  have h3 : r 3 = (20905 : ℝ) / 98304 := by
    show r (2 + 1) = (20905 : ℝ) / 98304
    rw [hr 2, h2]
    norm_num
  have h4 : r 4 = (48031 : ℝ) / 688128 := by
    show r (3 + 1) = (48031 : ℝ) / 688128
    rw [hr 3, h3]
    norm_num
  have h5 : r 5 = (3593 : ℝ) / 1146880 := by
    show r (4 + 1) = (3593 : ℝ) / 1146880
    rw [hr 4, h4]
    norm_num
  have h6 : r 6 = (3593 : ℝ) / 1146880 := by
    show r (5 + 1) = (3593 : ℝ) / 1146880
    rw [hr 5, h5]
    norm_num
  have h7 : r 7 = (3593 : ℝ) / 1146880 := by
    show r (6 + 1) = (3593 : ℝ) / 1146880
    rw [hr 6, h6]
    norm_num
  have h8 : r 8 = (3593 : ℝ) / 1146880 := by
    show r (7 + 1) = (3593 : ℝ) / 1146880
    rw [hr 7, h7]
    norm_num
  have h9 : r 9 = (3593 : ℝ) / 1146880 := by
    show r (8 + 1) = (3593 : ℝ) / 1146880
    rw [hr 8, h8]
    norm_num
  have h10 : r 10 = (98449 : ℝ) / 83722240 := by
    show r (9 + 1) = (98449 : ℝ) / 83722240
    rw [hr 9, h9]
    norm_num
  have h11 : r 11 = (16991087 : ℝ) / 85647851520 := by
    show r (10 + 1) = (16991087 : ℝ) / 85647851520
    rw [hr 10, h10]
    norm_num
  have h12 : r 12 = (16991087 : ℝ) / 85647851520 := by
    show r (11 + 1) = (16991087 : ℝ) / 85647851520
    rw [hr 11, h11]
    norm_num
  have h13 : r 13 = (16991087 : ℝ) / 85647851520 := by
    show r (12 + 1) = (16991087 : ℝ) / 85647851520
    rw [hr 12, h12]
    norm_num
  have h14 : r 14 = (53526142097 : ℝ) / 701541551800320 := by
    show r (13 + 1) = (53526142097 : ℝ) / 701541551800320
    rw [hr 13, h13]
    norm_num
  have h15 : r 15 = (19486359352759 : ℝ) / 1277039471460515840 := by
    show r (14 + 1) = (19486359352759 : ℝ) / 1277039471460515840
    rw [hr 14, h14]
    norm_num
  have h16 : r (15 + 1) = (19486359352759 : ℝ) / 1277039471460515840 := by
    rw [hr 15, h15]
    norm_num
  -- the tail after 16 is below the stalled remainder
  have hterm : ∀ k : ℕ, 1 ≤ k →
      (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ (1 / 2 : ℝ) ^ k + 2 * (1 / 4 : ℝ) ^ k := by
    intro k hk
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by rw [← mul_pow]; norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by linarith
    rw [one_div_pow, one_div_pow, div_le_iff₀ hpos]
    rw [h4]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    field_simp
    nlinarith
  have hnn : ∀ k : ℕ, 1 ≤ k → (0 : ℝ) ≤ (1 : ℝ) / ((2 : ℝ) ^ k - 1) := by
    intro k hk
    have : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    exact div_nonneg zero_le_one (by linarith)
  have hA : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (15 + 2 + i)) :=
    summable_geometric_two.comp_injective (add_right_injective (15 + 2))
  have hB : Summable (fun i : ℕ => 2 * (1 / 4 : ℝ) ^ (15 + 2 + i)) :=
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).comp_injective
      (add_right_injective (15 + 2))).mul_left 2
  have hAB : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (15 + 2 + i) + 2 * (1 / 4 : ℝ) ^ (15 + 2 + i)) := hA.add hB
  have hT : Summable (fun i : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (15 + 2 + i) - 1)) :=
    hAB.of_nonneg_of_le (fun i => hnn _ (by omega)) (fun i => hterm _ (by omega))
  have hle : ∑' (i : ℕ), (1 : ℝ) / ((2 : ℝ) ^ (15 + 2 + i) - 1)
      ≤ ∑' (i : ℕ), ((1 / 2 : ℝ) ^ (15 + 2 + i) + 2 * (1 / 4 : ℝ) ^ (15 + 2 + i)) :=
    Summable.tsum_le_tsum (fun i => hterm _ (by omega)) hT hAB
  have hvalA : ∑' (i : ℕ), (1 / 2 : ℝ) ^ (15 + 2 + i) = (1 / 2 : ℝ) ^ 17 * 2 := by
    have : (fun i : ℕ => (1 / 2 : ℝ) ^ (15 + 2 + i)) = fun i => (1 / 2 : ℝ) ^ (15 + 2) * (1 / 2 : ℝ) ^ i := by
      funext i
      rw [pow_add]
    rw [this, tsum_mul_left, tsum_geometric_two]
  have hvalB : ∑' (i : ℕ), 2 * (1 / 4 : ℝ) ^ (15 + 2 + i) = 2 * ((1 / 4 : ℝ) ^ 17 * (1 - 1 / 4)⁻¹) := by
    have : (fun i : ℕ => 2 * (1 / 4 : ℝ) ^ (15 + 2 + i)) = fun i => 2 * ((1 / 4 : ℝ) ^ (15 + 2) * (1 / 4 : ℝ) ^ i) := by
      funext i
      rw [pow_add]
    rw [this, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have hval : ∑' (i : ℕ), ((1 / 2 : ℝ) ^ (15 + 2 + i) + 2 * (1 / 4 : ℝ) ^ (15 + 2 + i))
      = (1 / 2 : ℝ) ^ 17 * 2 + 2 * ((1 / 4 : ℝ) ^ 17 * (1 - 1 / 4)⁻¹) := by
    rw [hA.tsum_add hB, hvalA, hvalB]
  refine ⟨15, 17891, r, 15, 16, ?_, hr, le_rfl, by norm_num, by norm_num, ?_, ?_⟩
  · rw [h0]
    norm_num
  · rw [h16]
    norm_num
  · rw [h16]
    have := hle
    rw [hval] at this
    refine lt_of_le_of_lt this ?_
    norm_num
