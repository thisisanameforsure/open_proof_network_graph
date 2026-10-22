-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    Irrational (∑' n : {n : ℕ | Squarefree n}, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro h
  apply h
  exact Nat.infinite_setOf_prime.mono (fun p hp => (Nat.prime_iff.mp hp).squarefree)
