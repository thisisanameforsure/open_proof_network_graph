-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    Irrational (∑' m : {m : ℕ | ∃ a b, m = a ^ 2 + b ^ 2}, (1 : ℝ) / (2 ^ m.1 - 1)) := by
  intro h
  apply h
  exact Set.infinite_of_injective_forall_mem (Nat.pow_left_injective two_ne_zero)
    (fun n => ⟨n, 0, by ring⟩)
