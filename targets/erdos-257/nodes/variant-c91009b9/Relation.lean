-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    ∀ A : Set ℕ, A.Infinite → A.Pairwise Nat.Coprime →
      Summable (fun n : A => (1 : ℝ) / n.1) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro h A hA _ _
  exact h A hA
