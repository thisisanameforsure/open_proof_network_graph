-- relation: partial
import Defs.IsPrime
import Mathlib.Tactic
import Nodes.«variant-f73fdb34».Context

/-! The root implies the variant (D-30, `partial`): apply the root at `max n 100`. -/

theorem relation :
    (∀ n : Nat, ∃ p : Nat, n < p ∧ Opn.IsPrime p) →
    (∀ n : Nat, ∃ p : Nat, n < p ∧ 100 ≤ p ∧ Opn.IsPrime p) := by
  intro h n
  obtain ⟨p, hlt, hp⟩ := h (max n 100)
  exact ⟨p, by omega, by omega, hp⟩
