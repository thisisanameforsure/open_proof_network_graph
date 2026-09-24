import Mathlib
import Nodes.«variant-bc28297c».Context

/-! Graham's gcd conjecture (Erdős problem 402) for five-element sets: with M the largest
element, if every b had gcd(M, b) > M/5 then every b would be (j/k)M with j ≤ k ≤ 4, and any
five of those six values contain a pair 9s, 8s or 8s, 3s or 9s, 4s whose gcd is s. -/

theorem Opn.erdos_402_card_five :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 5 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  intro A hA h5
  have hpos : 0 < A.card := by omega
  have hne : A.Nonempty := Finset.card_pos.mp hpos
  have key : ∀ a b : ℕ, a.gcd b * A.card ≤ a → (a.gcd b : ℚ) ≤ (a / A.card : ℚ) := by
    intro a b h
    rw [le_div_iff₀ (by exact_mod_cast hpos)]
    exact_mod_cast h
  have hM : A.max' hne ∈ A := Finset.max'_mem A hne
  have hMpos : 0 < A.max' hne := Nat.pos_of_ne_zero (fun h => hA (h ▸ hM))
  have aux : ∀ x ∈ A, x < A.max' hne →
      (A.max' hne).gcd x * 5 ≤ A.max' hne ∨ 2 * x = A.max' hne ∨ 3 * x = A.max' hne ∨
        3 * x = 2 * A.max' hne ∨ 4 * x = A.max' hne ∨ 4 * x = 3 * A.max' hne := by
    intro x hx hlt
    have hxpos : 0 < x := Nat.pos_of_ne_zero (fun h => hA (h ▸ hx))
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left (A.max' hne) x
    obtain ⟨j, hj⟩ := Nat.gcd_dvd_right (A.max' hne) x
    have hgpos : 0 < (A.max' hne).gcd x := Nat.gcd_pos_of_pos_right _ hxpos
    by_cases hk5 : 5 ≤ k
    · left
      calc (A.max' hne).gcd x * 5 ≤ (A.max' hne).gcd x * k := Nat.mul_le_mul_left _ hk5
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
      have hk' : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk' with rfl | rfl | rfl
      · have : j = 1 := by omega
        subst this
        omega
      · have : j = 1 ∨ j = 2 := by omega
        rcases this with rfl | rfl <;> omega
      · have : j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases this with rfl | rfl | rfl <;> omega
  have hle : ∀ x ∈ A, x ≠ A.max' hne → x < A.max' hne :=
    fun x hx hxM => lt_of_le_of_ne (Finset.le_max' A x hx) hxM
  have he : (A.erase (A.max' hne)).card = 4 := by
    rw [Finset.card_erase_of_mem hM, h5]
  by_cases hw : ∃ x ∈ A, x < A.max' hne ∧ (A.max' hne).gcd x * 5 ≤ A.max' hne
  · obtain ⟨x, hx, -, h⟩ := hw
    exact ⟨_, hM, x, hx, key _ x (by rw [h5]; exact h)⟩
  have forms : ∀ x ∈ A, x ≠ A.max' hne →
      2 * x = A.max' hne ∨ 3 * x = A.max' hne ∨ 3 * x = 2 * A.max' hne ∨
        4 * x = A.max' hne ∨ 4 * x = 3 * A.max' hne := by
    intro x hx hxM
    rcases aux x hx (hle x hx hxM) with h | h
    · exact absurd ⟨x, hx, hle x hx hxM, h⟩ hw
    · exact h
  have gdvd : ∀ u v c d : ℕ, u.gcd v ∣ c * v - d * u := fun u v c d =>
    Nat.dvd_sub (Dvd.dvd.mul_left (Nat.gcd_dvd_right u v) c)
      (Dvd.dvd.mul_left (Nat.gcd_dvd_left u v) d)
  have gdvd' : ∀ u v c d : ℕ, u.gcd v ∣ d * u - c * v := fun u v c d =>
    Nat.dvd_sub (Dvd.dvd.mul_left (Nat.gcd_dvd_left u v) d)
      (Dvd.dvd.mul_left (Nat.gcd_dvd_right u v) c)
  have sub3 : ∀ p q r : ℕ, (∀ x ∈ A, x ≠ A.max' hne → x = p ∨ x = q ∨ x = r) → False := by
    intro p q r h
    have hs : A.erase (A.max' hne) ⊆ {p, q, r} := by
      intro x hx
      rw [Finset.mem_erase] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact h x hx.2 hx.1
    have := (Finset.card_le_card hs).trans Finset.card_le_three
    omega
  by_cases hE : ∃ u ∈ A, 4 * u = 3 * A.max' hne
  · obtain ⟨u, hu, hu'⟩ := hE
    by_cases hB : ∃ v ∈ A, 3 * v = A.max' hne
    · obtain ⟨v, hv, hv'⟩ := hB
      refine ⟨u, hu, v, hv, key u v ?_⟩
      have := Nat.le_of_dvd (by omega) (gdvd' u v 2 1)
      rw [h5]
      omega
    by_cases hC : ∃ v ∈ A, 3 * v = 2 * A.max' hne
    · obtain ⟨v, hv, hv'⟩ := hC
      refine ⟨u, hu, v, hv, key u v ?_⟩
      have := Nat.le_of_dvd (by omega) (gdvd' u v 1 1)
      rw [h5]
      omega
    exfalso
    refine sub3 (A.max' hne / 2) (A.max' hne / 4) (3 * A.max' hne / 4) ?_
    intro x hx hxM
    rcases forms x hx hxM with h | h | h | h | h
    · omega
    · exact absurd ⟨x, hx, h⟩ hB
    · exact absurd ⟨x, hx, h⟩ hC
    · omega
    · omega
  · by_cases hC : ∃ u ∈ A, 3 * u = 2 * A.max' hne
    · obtain ⟨u, hu, hu'⟩ := hC
      by_cases hD : ∃ v ∈ A, 4 * v = A.max' hne
      · obtain ⟨v, hv, hv'⟩ := hD
        refine ⟨u, hu, v, hv, key u v ?_⟩
        have := Nat.le_of_dvd (by omega) (gdvd u v 3 1)
        rw [h5]
        omega
      exfalso
      refine sub3 (A.max' hne / 2) (A.max' hne / 3) (2 * A.max' hne / 3) ?_
      intro x hx hxM
      rcases forms x hx hxM with h | h | h | h | h
      · omega
      · omega
      · omega
      · exact absurd ⟨x, hx, h⟩ hD
      · exact absurd ⟨x, hx, h⟩ hE
    · exfalso
      refine sub3 (A.max' hne / 2) (A.max' hne / 3) (A.max' hne / 4) ?_
      intro x hx hxM
      rcases forms x hx hxM with h | h | h | h | h
      · omega
      · omega
      · exact absurd ⟨x, hx, h⟩ hC
      · omega
      · exact absurd ⟨x, hx, h⟩ hE
