import Defs.IsPrime
import Mathlib.Tactic

/-! Euclid's original formulation (Elements IX.20): no finite list contains all the primes.
Over the graph's own `Opn.IsPrime`: for every list of natural numbers there is a prime that is
not a member of it. -/

theorem Opn.no_finite_list_of_primes : ∀ l : List Nat, ∃ p : Nat, Opn.IsPrime p ∧ p ∉ l := by
  intro l
  have bound : ∀ x : Nat, x ∈ l → x ≤ l.sum := by
    intro x hx
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) x hx
  have euclid : ∀ n : Nat, ∃ p : Nat, n < p ∧ Opn.IsPrime p := by
    intro n
    have f1 : Nat.factorial (n + 1) + 1 ≠ 1 := by
      have := Nat.factorial_pos (n + 1)
      omega
    have pp : Nat.Prime (Nat.minFac (Nat.factorial (n + 1) + 1)) := Nat.minFac_prime f1
    refine ⟨Nat.minFac (Nat.factorial (n + 1) + 1), ?_, pp.two_le, ?_⟩
    · by_contra h
      have h₁ : Nat.minFac (Nat.factorial (n + 1) + 1) ∣ Nat.factorial (n + 1) :=
        Nat.dvd_factorial (Nat.minFac_pos _) (by omega)
      have h₂ : Nat.minFac (Nat.factorial (n + 1) + 1) ∣ 1 :=
        (Nat.dvd_add_iff_right h₁).2 (Nat.minFac_dvd _)
      exact pp.not_dvd_one h₂
    · intro d hd
      obtain ⟨c, hc⟩ := hd
      exact (Nat.dvd_prime pp).mp ⟨c, hc⟩
  obtain ⟨p, hlt, hp⟩ := euclid l.sum
  refine ⟨p, hp, fun hmem => ?_⟩
  have := bound p hmem
  omega
