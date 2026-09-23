import Mathlib
import Nodes.«variant-950630b9».Context

/-! Graham's gcd conjecture (Erdős problem 402) when the largest element of `A` is coprime
to some element of `A`: then that pair has gcd 1, and `|A| ≤ max A` because `A` is a set of
positive integers at most `max A`. -/

theorem Opn.erdos_402_max_coprime :
    ∀ (A : Finset ℕ), 0 ∉ A → (∃ m ∈ A, ∃ b ∈ A, (∀ c ∈ A, c ≤ m) ∧ m.Coprime b) →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  rintro A hA ⟨m, hm, b, hb, hmax, hcop⟩
  refine ⟨m, hm, b, hb, ?_⟩
  have hsub : A ⊆ Finset.Icc 1 m := by
    intro c hc
    rw [Finset.mem_Icc]
    refine ⟨Nat.pos_of_ne_zero ?_, hmax c hc⟩
    rintro rfl
    exact hA hc
  have hcard : A.card ≤ m := by
    have := Finset.card_le_card hsub
    simpa using this
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨m, hm⟩
  rw [Nat.Coprime] at hcop
  rw [hcop, le_div_iff₀ (by exact_mod_cast hpos)]
  simp only [Nat.cast_one, one_mul]
  exact_mod_cast hcard
