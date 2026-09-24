import Mathlib
import Nodes.«variant-780e7ade».Context

/-! Graham's gcd conjecture (Erdős problem 402) for four-element sets: with M the largest
element, if every b had gcd(M, b) > M/4 then every b would be one of M, M/2, M/3, 2M/3, and
the pair 2M/3, M/2 = 4t, 3t has gcd t, which is a quarter of 4t. -/

theorem Opn.erdos_402_card_four :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 4 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  intro A hA h4
  have hpos : 0 < A.card := by omega
  have hne : A.Nonempty := Finset.card_pos.mp hpos
  have key : ∀ a b : ℕ, a.gcd b * A.card ≤ a → (a.gcd b : ℚ) ≤ (a / A.card : ℚ) := by
    intro a b h
    rw [le_div_iff₀ (by exact_mod_cast hpos)]
    exact_mod_cast h
  have hM : A.max' hne ∈ A := Finset.max'_mem A hne
  have hMpos : 0 < A.max' hne := Nat.pos_of_ne_zero (fun h => hA (h ▸ hM))
  have aux : ∀ x ∈ A, x < A.max' hne →
      (A.max' hne).gcd x * 4 ≤ A.max' hne ∨ 2 * x = A.max' hne ∨ 3 * x = A.max' hne ∨
        3 * x = 2 * A.max' hne := by
    intro x hx hlt
    have hxpos : 0 < x := Nat.pos_of_ne_zero (fun h => hA (h ▸ hx))
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left (A.max' hne) x
    obtain ⟨j, hj⟩ := Nat.gcd_dvd_right (A.max' hne) x
    have hgpos : 0 < (A.max' hne).gcd x := Nat.gcd_pos_of_pos_right _ hxpos
    by_cases hk4 : 4 ≤ k
    · left
      calc (A.max' hne).gcd x * 4 ≤ (A.max' hne).gcd x * k := Nat.mul_le_mul_left _ hk4
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
      have hk' : k = 2 ∨ k = 3 := by omega
      rcases hk' with rfl | rfl
      · have : j = 1 := by omega
        subst this
        omega
      · have : j = 1 ∨ j = 2 := by omega
        rcases this with rfl | rfl <;> omega
  have win : ∀ x ∈ A, (A.max' hne).gcd x * 4 ≤ A.max' hne →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) :=
    fun x hx h => ⟨_, hM, x, hx, key _ x (by rw [h4]; exact h)⟩
  have fin : ∀ u ∈ A, ∀ v ∈ A, 3 * u = 2 * A.max' hne → 2 * v = A.max' hne →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
    intro u hu v hv hu' hv'
    refine ⟨u, hu, v, hv, key u v ?_⟩
    have hd : u.gcd v ∣ u - v := Nat.dvd_sub (Nat.gcd_dvd_left u v) (Nat.gcd_dvd_right u v)
    have hle : u.gcd v ≤ u - v := Nat.le_of_dvd (by omega) hd
    rw [h4]
    omega
  have he : (A.erase (A.max' hne)).card = 3 := by
    rw [Finset.card_erase_of_mem hM, h4]
  obtain ⟨x, y, z, hxy, hxz, hyz, hexyz⟩ := Finset.card_eq_three.mp he
  have hx : x ∈ A.erase (A.max' hne) := by rw [hexyz]; simp
  have hy : y ∈ A.erase (A.max' hne) := by rw [hexyz]; simp
  have hz : z ∈ A.erase (A.max' hne) := by rw [hexyz]; simp
  rw [Finset.mem_erase] at hx hy hz
  have hxlt : x < A.max' hne := lt_of_le_of_ne (Finset.le_max' A x hx.2) hx.1
  have hylt : y < A.max' hne := lt_of_le_of_ne (Finset.le_max' A y hy.2) hy.1
  have hzlt : z < A.max' hne := lt_of_le_of_ne (Finset.le_max' A z hz.2) hz.1
  rcases aux x hx.2 hxlt with h1 | h1 | h1 | h1 <;>
  rcases aux y hy.2 hylt with h2 | h2 | h2 | h2 <;>
  rcases aux z hz.2 hzlt with h3 | h3 | h3 | h3 <;>
  first
    | exact win x hx.2 h1
    | exact win y hy.2 h2
    | exact win z hz.2 h3
    | (exfalso; omega)
    | exact fin x hx.2 y hy.2 h1 h2
    | exact fin x hx.2 z hz.2 h1 h3
    | exact fin y hy.2 x hx.2 h2 h1
    | exact fin y hy.2 z hz.2 h2 h3
    | exact fin z hz.2 x hx.2 h3 h1
    | exact fin z hz.2 y hy.2 h3 h2
