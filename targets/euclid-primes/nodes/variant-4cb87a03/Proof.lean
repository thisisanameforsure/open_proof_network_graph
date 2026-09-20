import Defs.IsPrime
import Mathlib.Tactic

/-! Euclid's explicit bound, over the graph's own `IsPrime`: for every `n` there is a prime `p`
with `n < p ≤ n! + 1`. A strengthening of the root `Opn.infinitude_of_primes` (drop the middle
conjunct to recover it). `n !` is Mathlib's `Nat.factorial`, as in the root's merged holes. -/

theorem Opn.euclid_explicit_bound : ∀ n : Nat, ∃ p : Nat, n < p ∧ p ≤ Nat.factorial n + 1 ∧ Opn.IsPrime p := by
  intro n
  have prime_divisor : ∀ m : Nat, 2 ≤ m → ∃ p, Opn.IsPrime p ∧ Opn.Divides p m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases hp : Opn.IsPrime m
      · exact ⟨m, hp, 1, by simp⟩
      · have hex : ∃ d, Opn.Divides d m ∧ d ≠ 1 ∧ d ≠ m := by
          by_contra hcon
          apply hp
          refine ⟨hm, fun d hd => ?_⟩
          by_contra h
          exact hcon ⟨d, hd, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
        obtain ⟨d, ⟨c, hc⟩, hd1, hdm⟩ := hex
        have hd0 : d ≠ 0 := by
          rintro rfl
          simp at hc
          omega
        have hc0 : c ≠ 0 := by
          rintro rfl
          simp at hc
          omega
        have hc1 : c ≠ 1 := by
          rintro rfl
          simp at hc
          exact hdm hc.symm
        have hdlt : d < m := by
          have h2 : d * 2 ≤ d * c := Nat.mul_le_mul_left d (by omega)
          omega
        obtain ⟨p, hp', q, hq⟩ := ih d hdlt (by omega)
        exact ⟨p, hp', q * c, by rw [hc, hq, Nat.mul_assoc]⟩
  have hpos : 0 < Nat.factorial n := Nat.factorial_pos n
  obtain ⟨p, hp, c, hc⟩ := prime_divisor (Nat.factorial n + 1) (by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hple : p ≤ Nat.factorial n + 1 := by
    rw [hc]
    exact Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hc0)
  refine ⟨p, ?_, hple, hp⟩
  by_contra hnp
  have hpn : p ≤ n := by omega
  have hp2 := hp.1
  obtain ⟨e, he⟩ := Nat.dvd_factorial (by omega : 0 < p) hpn
  have hec : e < c := by
    by_contra h
    have h' : p * c ≤ p * e := Nat.mul_le_mul_left p (by omega)
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hec
  have hexp : p * (e + k + 1) = p * e + p * k + p := by ring
  omega
