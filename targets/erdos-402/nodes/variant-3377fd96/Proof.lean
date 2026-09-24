import Mathlib
import Nodes.«variant-3377fd96».Context

/-! Graham's gcd conjecture (Erdős problem 402) when some element `x` of `A` has no prime factor
below `|A|`: either `x` divides every element, and then the largest element is at least `|A| * x`,
or `gcd(x, b) < x` for some `b`, and then `x / gcd(x, b)` is a divisor of `x` above 1, so at
least `x.minFac ≥ |A|`. Contains the case of a prime `p ≥ |A|` in `A`. -/

theorem Opn.erdos_402_minFac :
    ∀ (A : Finset ℕ), 0 ∉ A → ∀ x ∈ A, A.card ≤ x.minFac →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  intro A hA x hx hmin
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hxpos : 0 < x := Nat.pos_of_ne_zero (fun h => hA (h ▸ hx))
  have key : ∀ a b : ℕ, a.gcd b * A.card ≤ a → (a.gcd b : ℚ) ≤ (a / A.card : ℚ) := by
    intro a b h
    rw [le_div_iff₀ (by exact_mod_cast hpos)]
    exact_mod_cast h
  by_cases hc : ∃ b ∈ A, x.gcd b < x
  · obtain ⟨b, hb, hlt⟩ := hc
    refine ⟨x, hx, b, hb, key x b ?_⟩
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left x b
    have hk2 : 2 ≤ k := by
      by_contra hcon
      push_neg at hcon
      interval_cases k
      · rw [mul_zero] at hk
        omega
      · rw [mul_one] at hk
        omega
    have hmk : x.minFac ≤ k := Nat.minFac_le_of_dvd hk2 ⟨x.gcd b, by rw [mul_comm]; exact hk⟩
    calc x.gcd b * A.card ≤ x.gcd b * k := Nat.mul_le_mul_left _ (hmin.trans hmk)
      _ = x := hk.symm
  · push_neg at hc
    have hdvd : ∀ b ∈ A, x ∣ b := fun b hb => by
      have h3 : x.gcd b = x := le_antisymm (Nat.gcd_le_left b hxpos) (hc b hb)
      rw [← h3]
      exact Nat.gcd_dvd_right x b
    have hMA : A.max' ⟨x, hx⟩ ∈ A := Finset.max'_mem A _
    refine ⟨A.max' ⟨x, hx⟩, hMA, x, hx, key _ x ?_⟩
    rw [Nat.gcd_eq_right (hdvd _ hMA)]
    have hsub : A ⊆ (Finset.Icc 1 (A.max' ⟨x, hx⟩ / x)).image (fun k => x * k) := by
      intro b hb
      obtain ⟨k, rfl⟩ := hdvd b hb
      rw [Finset.mem_image]
      refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          rw [mul_zero] at hb
          exact absurd hb hA
        · exact h
      · rw [Nat.le_div_iff_mul_le hxpos, mul_comm]
        exact Finset.le_max' A _ hb
    have hcard : A.card ≤ A.max' ⟨x, hx⟩ / x :=
      calc A.card ≤ _ := Finset.card_le_card hsub
        _ ≤ (Finset.Icc 1 (A.max' ⟨x, hx⟩ / x)).card := Finset.card_image_le
        _ = A.max' ⟨x, hx⟩ / x := by simp
    calc x * A.card ≤ x * (A.max' ⟨x, hx⟩ / x) := Nat.mul_le_mul_left x hcard
      _ ≤ A.max' ⟨x, hx⟩ := Nat.mul_div_le _ x
