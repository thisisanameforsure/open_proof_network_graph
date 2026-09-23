import Mathlib

theorem witness : ∃ (A : Finset ℕ) (x : ℕ), 0 ∉ A ∧ x ∈ A ∧ A.card ≤ x.minFac :=
  ⟨{2, 3}, 3, by decide, by simp, by rw [Finset.card_pair (by norm_num)]; norm_num⟩
