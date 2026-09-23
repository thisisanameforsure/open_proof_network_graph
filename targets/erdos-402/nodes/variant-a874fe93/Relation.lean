-- relation: partial
import Mathlib

theorem relation :
    (∀ (A : Finset ℕ), 0 ∉ A → A.Nonempty → ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ)) →
    (∀ (A : Finset ℕ), 0 ∉ A → ∀ p ∈ A, p.Prime → A.card ≤ p →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ)) := by
  intro h A hA p hp _ _
  obtain ⟨a, ha, b, hb, hab⟩ := h A hA ⟨p, hp⟩
  exact ⟨a, ha, b, hb, hab⟩
