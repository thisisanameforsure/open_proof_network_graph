-- relation: partial
import Mathlib
import Nodes.«variant-cff52b79».Context

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    (∀ (A : Set ℕ),
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) ∨
      Irrational (∑' n : ↥Aᶜ, (1 : ℝ) / (2 ^ n.1 - 1))) := by
  intro h A
  by_cases hA : A.Finite
  · exact Or.inr (h Aᶜ hA.infinite_compl)
  · exact Or.inl (h A hA)
