-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    ∀ k : ℕ, 0 < k →
      Irrational (∑' m : {m : ℕ | ∃ n, m = n ^ k}, (1 : ℝ) / (2 ^ m.1 - 1)) := by
  intro h k hk
  apply h
  exact Set.infinite_of_injective_forall_mem (Nat.pow_left_injective hk.ne') (fun n => ⟨n, rfl⟩)
