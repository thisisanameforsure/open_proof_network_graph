import Defs.IsPrime
import Mathlib.Tactic

/-! Infinitely many primes congruent to 3 modulo 4, over the graph's own `IsPrime`: for every
`n` there is a prime `p > n` with `p % 4 = 3`. A strengthening of Euclid's theorem (the root). -/

theorem Opn.infinitude_of_primes_three_mod_four : ∀ n : Nat, ∃ p : Nat, n < p ∧ Opn.IsPrime p ∧ p % 4 = 3 := by
  intro n
  have bridge : ∀ p : Nat, Nat.Prime p → Opn.IsPrime p := by
    intro p hp
    refine ⟨hp.two_le, ?_⟩
    intro d hd
    have hd' : d ∣ p := by
      obtain ⟨c, hc⟩ := hd
      exact ⟨c, hc⟩
    exact (Nat.dvd_prime hp).mp hd'
  have key : ∀ m : Nat, m % 4 = 3 → ∃ p : Nat, Nat.Prime p ∧ p ∣ m ∧ p % 4 = 3 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases hp : Nat.Prime m
      · exact ⟨m, hp, dvd_rfl, hm⟩
      · have h2 : 2 ≤ m := by omega
        obtain ⟨a, ha, ha2, ham⟩ := Nat.exists_dvd_of_not_prime2 h2 hp
        obtain ⟨b, hb⟩ := ha
        have hbpos : 0 < b := by
          rcases Nat.eq_zero_or_pos b with h | h
          · subst h; omega
          · exact h
        have hbm : b < m := by
          rw [hb]; nlinarith
        have hmod := Nat.mul_mod a b 4
        rw [← hb, hm] at hmod
        have hcases : a % 4 = 3 ∨ b % 4 = 3 := by
          rcases (by omega : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3) with h | h | h | h <;>
          rcases (by omega : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3) with h' | h' | h' | h' <;>
          rw [h, h'] at hmod <;> omega
        rcases hcases with h | h
        · obtain ⟨p, hp1, hp2, hp3⟩ := ih a ham h
          exact ⟨p, hp1, dvd_trans hp2 ⟨b, hb⟩, hp3⟩
        · obtain ⟨p, hp1, hp2, hp3⟩ := ih b hbm h
          exact ⟨p, hp1, dvd_trans hp2 ⟨a, by rw [hb, Nat.mul_comm]⟩, hp3⟩
  have hfact : 0 < Nat.factorial n := Nat.factorial_pos n
  obtain ⟨p, hp, hpd, hp3⟩ := key (4 * Nat.factorial n - 1) (by omega)
  refine ⟨p, ?_, bridge p hp, hp3⟩
  rcases Nat.lt_or_ge n p with h | h
  · exact h
  · exfalso
    have h1 : p ∣ Nat.factorial n := Nat.dvd_factorial hp.pos h
    have h4 : p ∣ 4 * Nat.factorial n := Dvd.dvd.mul_left h1 4
    have hone : p ∣ 1 := by
      have := (Nat.dvd_sub h4 hpd)
      have e : 4 * Nat.factorial n - (4 * Nat.factorial n - 1) = 1 := by omega
      rwa [e] at this
    have := Nat.le_of_dvd Nat.one_pos hone
    have := hp.two_le
    omega
