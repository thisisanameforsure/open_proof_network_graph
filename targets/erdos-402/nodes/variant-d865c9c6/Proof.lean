import Mathlib
import Nodes.«variant-d865c9c6».Context

/-! Graham's gcd conjecture (Erdős problem 402) for two-element sets: the larger element's
gcd with the smaller is a proper divisor of it, so it is at most half of it. -/

theorem Opn.erdos_402_card_two :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 2 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  intro A hA hc
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
  have hx0 : x ≠ 0 := by
    intro h; apply hA; simp [h]
  have hy0 : y ≠ 0 := by
    intro h; apply hA; simp [h]
  have key : ∀ p q : ℕ, p ≠ 0 → q ≠ 0 → p < q → ((q.gcd p : ℕ) : ℚ) ≤ (q : ℚ) / 2 := by
    intro p q hp hq hpq
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left q p
    have hgle : q.gcd p ≤ p := Nat.le_of_dvd (Nat.pos_of_ne_zero hp) (Nat.gcd_dvd_right q p)
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push_neg at hlt
      interval_cases k
      · exact hq (by rw [hk, mul_zero])
      · rw [mul_one] at hk
        omega
    have h2 : 2 * q.gcd p ≤ q := by
      calc 2 * q.gcd p = q.gcd p * 2 := by ring
        _ ≤ q.gcd p * k := Nat.mul_le_mul_left _ hk2
        _ = q := hk.symm
    rw [le_div_iff₀ (by norm_num : (0:ℚ) < 2)]
    have : ((2 * q.gcd p : ℕ) : ℚ) ≤ (q : ℚ) := by exact_mod_cast h2
    push_cast at this
    linarith
  rw [hc]
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨y, by simp, x, by simp, by exact_mod_cast key x y hx0 hy0 h⟩
  · exact ⟨x, by simp, y, by simp, by exact_mod_cast key y x hy0 hx0 h⟩
