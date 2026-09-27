import Mathlib
import Nodes.«variant-a3b3cb8f».Context

/-! Graham's gcd conjecture (Erdős problem 402) for 7-element sets: with M the largest element,
if every b had gcd(M, b) > M/7 then every other element would be (j/k)M with j < k < 7, and a
finite check shows any 6 of those values contain a pair whose gcd is at most the larger over 7. -/

theorem Opn.erdos_402_card_seven :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 7 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  intro A hA hn
  have hpos : 0 < A.card := by omega
  have hne : A.Nonempty := Finset.card_pos.mp hpos
  have key : ∀ a b : ℕ, a.gcd b * A.card ≤ a → (a.gcd b : ℚ) ≤ (a / A.card : ℚ) := by
    intro a b h
    rw [le_div_iff₀ (by exact_mod_cast hpos)]
    exact_mod_cast h
  have hM : A.max' hne ∈ A := Finset.max'_mem A hne
  have hMpos : 0 < A.max' hne := Nat.pos_of_ne_zero (fun h => hA (h ▸ hM))
  by_cases hw : ∃ x ∈ A, (A.max' hne).gcd x * 7 ≤ A.max' hne
  · obtain ⟨x, hx, h⟩ := hw
    exact ⟨_, hM, x, hx, key _ x (by rw [hn]; exact h)⟩
  push_neg at hw
  have forms : ∀ x ∈ A.erase (A.max' hne), ∃ a ∈ ({10, 12, 15, 20, 24, 30, 36, 40, 45, 48, 50} : Finset ℕ), 60 * x = a * A.max' hne := by
    intro x hx
    rw [Finset.mem_erase] at hx
    have hxpos : 0 < x := Nat.pos_of_ne_zero (fun h => hA (h ▸ hx.2))
    have hlt : x < A.max' hne := lt_of_le_of_ne (Finset.le_max' A x hx.2) hx.1
    have hg := hw x hx.2
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left (A.max' hne) x
    obtain ⟨j, hj⟩ := Nat.gcd_dvd_right (A.max' hne) x
    have hgpos : 0 < (A.max' hne).gcd x := Nat.gcd_pos_of_pos_right _ hxpos
    have hkN : k < 7 := by
      by_contra hh
      push_neg at hh
      have := Nat.mul_le_mul_left ((A.max' hne).gcd x) hh
      omega
    have hjk : j < k := by
      by_contra hh
      push_neg at hh
      have := Nat.mul_le_mul_left ((A.max' hne).gcd x) hh
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        omega
      · exact h
    refine ⟨60 * j / k, ?_, ?_⟩
    · interval_cases k <;> interval_cases j <;> decide
    · interval_cases k <;> interval_cases j <;> omega
  have hcard : (A.erase (A.max' hne)).card = 6 := by
    rw [Finset.card_erase_of_mem hM, hn]
  have hS : ∀ a ∈ ({10, 12, 15, 20, 24, 30, 36, 40, 45, 48, 50} : Finset ℕ), (fun a : ℕ => if a = 10 then 0 else if a = 12 then 1 else if a = 15 then 2 else if a = 20 then 3 else if a = 24 then 0 else if a = 30 then 4 else if a = 36 then 2 else if a = 40 then 1 else if a = 45 then 0 else if a = 48 then 3 else if a = 50 then 2 else 0) a < 5 := by decide
  have hmaps : ∀ x ∈ A.erase (A.max' hne), (fun a : ℕ => if a = 10 then 0 else if a = 12 then 1 else if a = 15 then 2 else if a = 20 then 3 else if a = 24 then 0 else if a = 30 then 4 else if a = 36 then 2 else if a = 40 then 1 else if a = 45 then 0 else if a = 48 then 3 else if a = 50 then 2 else 0) (60 * x / A.max' hne) ∈ Finset.range 5 := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := forms x hx
    rw [Finset.mem_range, hax, Nat.mul_div_cancel _ hMpos]
    exact hS a ha
  obtain ⟨x, hx, y, hy, hxy, hc⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hcard, Finset.card_range]; norm_num) hmaps
  obtain ⟨a, ha, hax⟩ := forms x hx
  obtain ⟨b, hb, hby⟩ := forms y hy
  rw [hax, hby, Nat.mul_div_cancel _ hMpos, Nat.mul_div_cancel _ hMpos] at hc
  have hab : a ≠ b := by
    intro h
    subst h
    apply hxy
    omega
  have hpair : ∀ a ∈ ({10, 12, 15, 20, 24, 30, 36, 40, 45, 48, 50} : Finset ℕ), ∀ b ∈ ({10, 12, 15, 20, 24, 30, 36, 40, 45, 48, 50} : Finset ℕ), a ≠ b → (fun a : ℕ => if a = 10 then 0 else if a = 12 then 1 else if a = 15 then 2 else if a = 20 then 3 else if a = 24 then 0 else if a = 30 then 4 else if a = 36 then 2 else if a = 40 then 1 else if a = 45 then 0 else if a = 48 then 3 else if a = 50 then 2 else 0) a = (fun a : ℕ => if a = 10 then 0 else if a = 12 then 1 else if a = 15 then 2 else if a = 20 then 3 else if a = 24 then 0 else if a = 30 then 4 else if a = 36 then 2 else if a = 40 then 1 else if a = 45 then 0 else if a = 48 then 3 else if a = 50 then 2 else 0) b →
      7 * a.gcd b ≤ a ∨ 7 * a.gcd b ≤ b := by decide
  have hgcd : a.gcd b * A.max' hne = 60 * x.gcd y := by
    have h1 : Nat.gcd (60 * x) (60 * y) = 60 * x.gcd y := Nat.gcd_mul_left 60 x y
    rw [hax, hby, Nat.gcd_mul_right] at h1
    exact h1
  have hxA := (Finset.mem_erase.mp hx).2
  have hyA := (Finset.mem_erase.mp hy).2
  rcases hpair a ha b hb hab hc with h | h
  · refine ⟨x, hxA, y, hyA, key x y ?_⟩
    rw [hn]
    have h2 := Nat.mul_le_mul_right (A.max' hne) h
    have h3 : x.gcd y * 7 * 60 ≤ x * 60 := by nlinarith
    exact Nat.le_of_mul_le_mul_right h3 (by norm_num)
  · refine ⟨y, hyA, x, hxA, key y x ?_⟩
    rw [hn, Nat.gcd_comm]
    have h2 := Nat.mul_le_mul_right (A.max' hne) h
    have h3 : x.gcd y * 7 * 60 ≤ y * 60 := by nlinarith
    exact Nat.le_of_mul_le_mul_right h3 (by norm_num)
