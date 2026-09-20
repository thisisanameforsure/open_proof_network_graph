-- relation: resolves
import Defs.IsPrime
import Mathlib.Tactic

theorem relation : (∀ n : Nat, ∃ p : Nat, n < p ∧ Opn.IsPrime p ∧ p % 4 = 3) → (∀ n : Nat, ∃ p : Nat, n < p ∧ Opn.IsPrime p) := by
  intro h n
  obtain ⟨p, h1, h2, _⟩ := h n
  exact ⟨p, h1, h2⟩
