import Mathlib
import Nodes.«variant-3377fd96».Context

/-! Graham's gcd conjecture (Erdős problem 402) when some element `x` of `A` has no prime factor
below `|A|`: either `x` divides every element, and then the largest element is at least `|A| * x`,
or `gcd(x, b) < x` for some `b`, and then `x / gcd(x, b)` is a divisor of `x` above 1, so at
least `x.minFac ≥ |A|`. Contains the case of a prime `p ≥ |A|` in `A`. -/

theorem Opn.erdos_402_minFac :
    ∀ (A : Finset ℕ), 0 ∉ A → ∀ x ∈ A, A.card ≤ x.minFac →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  intro A hA0 x hx hn
  have hxpos : 0 < x := Nat.pos_of_ne_zero (fun h => hA0 (h ▸ hx))
  have hcard : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hcardQ : (0:ℚ) < A.card := by exact_mod_cast hcard
  by_cases h : ∃ b ∈ A, ¬ x ∣ b
  · obtain ⟨b, hb, hxb⟩ := h
    refine ⟨x, hx, b, hb, ?_⟩
    have hgpos : 0 < x.gcd b := Nat.gcd_pos_of_pos_left b hxpos
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left x b
    have hk1 : k ≠ 1 := by
      rintro rfl
      apply hxb
      have h2 : x = x.gcd b := by rw [mul_one] at hk; exact hk
      rw [h2]
      exact Nat.gcd_dvd_right x b
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk; omega
      · exact h0
    have hkdvd : k ∣ x := ⟨x.gcd b, by rw [mul_comm]; exact hk⟩
    have hmin : x.minFac ≤ k := Nat.minFac_le_of_dvd (by omega) hkdvd
    have hnk : A.card ≤ k := le_trans hn hmin
    rw [le_div_iff₀ hcardQ]
    have key : x.gcd b * A.card ≤ x := by
      calc x.gcd b * A.card ≤ x.gcd b * k := Nat.mul_le_mul_left _ hnk
        _ = x := hk.symm
    exact_mod_cast key
  · push Not at h
    have hne : A.Nonempty := ⟨x, hx⟩
    have hMA : A.max' hne ∈ A := Finset.max'_mem A hne
    have hxM : x ∣ A.max' hne := h _ hMA
    refine ⟨A.max' hne, hMA, x, hx, ?_⟩
    have hgcd : (A.max' hne).gcd x = x := Nat.gcd_eq_right hxM
    rw [hgcd, le_div_iff₀ hcardQ]
    have hsub : A ⊆ (Finset.Icc 1 (A.max' hne / x)).image (fun i => x * i) := by
      intro b hb
      obtain ⟨i, rfl⟩ := h b hb
      rw [Finset.mem_image]
      refine ⟨i, ?_, rfl⟩
      rw [Finset.mem_Icc]
      constructor
      · rcases Nat.eq_zero_or_pos i with h0 | h0
        · exfalso; apply hA0; rw [h0, mul_zero] at hb; exact hb
        · exact h0
      · rw [Nat.le_div_iff_mul_le hxpos, mul_comm]
        exact Finset.le_max' A _ hb
    have hc : A.card ≤ A.max' hne / x := by
      calc A.card ≤ ((Finset.Icc 1 (A.max' hne / x)).image (fun i => x * i)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.Icc 1 (A.max' hne / x)).card := Finset.card_image_le
        _ = A.max' hne / x := by simp
    have key : x * A.card ≤ A.max' hne := by
      calc x * A.card ≤ x * (A.max' hne / x) := Nat.mul_le_mul_left x hc
        _ ≤ A.max' hne := Nat.mul_div_le _ x
    exact_mod_cast key
