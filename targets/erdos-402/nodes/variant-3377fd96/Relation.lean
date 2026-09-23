-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Finset ℕ), 0 ∉ A → A.Nonempty → ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ)) →
    (∀ (A : Finset ℕ), 0 ∉ A → ∀ x ∈ A, A.card ≤ x.minFac →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ)) := by
  intro h A hA x hx _
  exact h A hA ⟨x, hx⟩
