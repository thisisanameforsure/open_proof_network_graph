import Mathlib
import Nodes.«variant-a874fe93».Context

/-! Graham's gcd conjecture (Erdős problem 402) when `A` contains a prime `p ≥ |A|`. If some
`b ∈ A` is not a multiple of `p`, the pair `(p, b)` has gcd 1 and `1 ≤ p / |A|`. Otherwise every
element is a multiple of `p` at most `max A`, so `|A| ≤ max A / p`, and the pair `(max A, p)` has
gcd `p ≤ max A / |A|`. -/

theorem Opn.erdos_402_large_prime :
    ∀ (A : Finset ℕ), 0 ∉ A → ∀ p ∈ A, p.Prime → A.card ≤ p →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  intro A hA0 x hx hxp hn0
  have hn : A.card ≤ x.minFac := by rw [hxp.minFac_eq]; exact hn0
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
