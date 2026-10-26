-- relation: partial
import Mathlib

theorem relation :
    (∀ t ≥ 1, ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = a}.ncard = t) →
      ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = a}.ncard = 1 :=
  fun h => h 1 (by norm_num)
