-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    Irrational (∑' p : {p : ℕ | p.Prime}, (1 : ℝ) / (2 ^ p.1 - 1)) := by
  intro h
  exact h _ Nat.infinite_setOf_prime
