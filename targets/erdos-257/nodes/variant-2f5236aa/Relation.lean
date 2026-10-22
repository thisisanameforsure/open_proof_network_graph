-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    Irrational (∑' n : ℕ, (1 : ℝ) / (2 ^ n - 1)) := by
  intro h
  have h' := h Set.univ Set.infinite_univ
  rwa [tsum_univ (f := fun n : ℕ => (1 : ℝ) / (2 ^ n - 1))] at h'
