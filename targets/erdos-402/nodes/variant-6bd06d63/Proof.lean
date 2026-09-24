import Mathlib
import Nodes.«variant-6bd06d63».Context

/-! Graham's gcd conjecture (Erdős problem 402) for three-element sets: with M the largest
element, if every b had gcd(M, b) > M/3 then every b would be M or M/2, so A has at most two
elements. -/

theorem Opn.erdos_402_card_three :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 3 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  intro A hA h3
  have hpos : 0 < A.card := by omega
  have hne : A.Nonempty := Finset.card_pos.mp hpos
  have key : ∀ a b : ℕ, a.gcd b * A.card ≤ a → (a.gcd b : ℚ) ≤ (a / A.card : ℚ) := by
    intro a b h
    rw [le_div_iff₀ (by exact_mod_cast hpos)]
    exact_mod_cast h
  have hM : A.max' hne ∈ A := Finset.max'_mem A hne
  have aux : ∀ x ∈ A, x < A.max' hne →
      (A.max' hne).gcd x * 3 ≤ A.max' hne ∨ 2 * x = A.max' hne := by
    intro x hx hlt
    have hxpos : 0 < x := Nat.pos_of_ne_zero (fun h => hA (h ▸ hx))
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left (A.max' hne) x
    obtain ⟨j, hj⟩ := Nat.gcd_dvd_right (A.max' hne) x
    have hgpos : 0 < (A.max' hne).gcd x := Nat.gcd_pos_of_pos_right _ hxpos
    by_cases hk3 : 3 ≤ k
    · left
      calc (A.max' hne).gcd x * 3 ≤ (A.max' hne).gcd x * k := Nat.mul_le_mul_left _ hk3
        _ = A.max' hne := hk.symm
    · right
      have hjk : j < k := by
        by_contra hh
        push_neg at hh
        have : (A.max' hne).gcd x * k ≤ (A.max' hne).gcd x * j := Nat.mul_le_mul_left _ hh
        omega
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h
          omega
        · exact h
      have hk2 : k = 2 := by omega
      have hj2 : j = 1 := by omega
      subst hk2 hj2
      omega
  have he : (A.erase (A.max' hne)).card = 2 := by
    rw [Finset.card_erase_of_mem hM, h3]
  obtain ⟨x, y, hxy, hexy⟩ := Finset.card_eq_two.mp he
  have hx : x ∈ A.erase (A.max' hne) := by rw [hexy]; simp
  have hy : y ∈ A.erase (A.max' hne) := by rw [hexy]; simp
  rw [Finset.mem_erase] at hx hy
  have hxlt : x < A.max' hne := lt_of_le_of_ne (Finset.le_max' A x hx.2) hx.1
  have hylt : y < A.max' hne := lt_of_le_of_ne (Finset.le_max' A y hy.2) hy.1
  rcases aux x hx.2 hxlt with h | h
  · exact ⟨_, hM, x, hx.2, key _ x (by rw [h3]; exact h)⟩
  rcases aux y hy.2 hylt with h' | h'
  · exact ⟨_, hM, y, hy.2, key _ y (by rw [h3]; exact h')⟩
  exact absurd (by omega : x = y) hxy
