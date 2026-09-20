-- relation: resolves
import Defs.IsPrime
import Mathlib.Tactic

/-! The variant implies the root (D-30, `resolves`): drop the bound `p ≤ n! + 1`. -/

theorem relation :
    (∀ n : Nat, ∃ p : Nat, n < p ∧ p ≤ Nat.factorial n + 1 ∧ Opn.IsPrime p) →
    (∀ n : Nat, ∃ p : Nat, n < p ∧ Opn.IsPrime p) :=
  fun h n => (h n).elim fun p hp => ⟨p, hp.1, hp.2.2⟩
