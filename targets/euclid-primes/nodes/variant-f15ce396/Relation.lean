-- relation: resolves
import Defs.IsPrime
import Mathlib.Tactic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Nat.Prime.Infinite

/-! The variant implies the root (D-30, resolves): an infinite set of naturals has an element
above any bound. -/

theorem relation :
    ({p : Nat | Opn.IsPrime p}.Infinite) →
    (∀ n : Nat, ∃ p : Nat, n < p ∧ Opn.IsPrime p) := by
  intro h n
  obtain ⟨p, hp, hlt⟩ := h.exists_gt n
  exact ⟨p, hlt, hp⟩
