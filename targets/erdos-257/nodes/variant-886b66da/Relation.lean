-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    ∀ a d : ℕ, 0 < d →
      Irrational (∑' m : {m : ℕ | ∃ n, m = a + d * n}, (1 : ℝ) / (2 ^ m.1 - 1)) := by
  intro h a d hd
  apply h
  have hinj : Function.Injective (fun n : ℕ => a + d * n) := by
    intro x y hxy
    have : d * x = d * y := by simpa using hxy
    exact Nat.eq_of_mul_eq_mul_left hd this
  exact Set.infinite_of_injective_forall_mem hinj (fun n => ⟨n, rfl⟩)
