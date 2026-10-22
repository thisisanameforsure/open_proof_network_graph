-- relation: partial
import Mathlib

/-! The variant is a partial form of the root (D-30, `partial`): the root, applied to the
infinite union of finitely many fast-growing sequences. -/

theorem relation :
    (∀ (A : Set ℕ), A.Infinite → Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))) →
    ∀ (r : ℕ) (c : Fin r → ℕ → ℕ), 0 < r → (∀ i, 0 < c i 0) →
    (∀ i j, (2 * r + 1) ^ (r + 1) * c i j ≤ c i (j + 1)) →
    Irrational (∑' n : (⋃ i, Set.range (c i) : Set ℕ), (1 : ℝ) / (2 ^ n.1 - 1)) := by
  intro h r c hr h0 hR
  apply h
  apply Set.Infinite.mono (Set.subset_iUnion (fun i => Set.range (c i)) ⟨0, hr⟩)
  apply Set.infinite_range_of_injective
  have h2 : 2 ≤ (2 * r + 1) ^ (r + 1) :=
    calc 2 ≤ 2 * r + 1 := by omega
      _ = (2 * r + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 * r + 1) ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hgt : ∀ j, j < c ⟨0, hr⟩ j := by
    intro j
    induction j with
    | zero => exact h0 _
    | succ j ih =>
      have a := hR ⟨0, hr⟩ j
      have b : 2 * c ⟨0, hr⟩ j ≤ (2 * r + 1) ^ (r + 1) * c ⟨0, hr⟩ j := Nat.mul_le_mul_right _ h2
      omega
  apply StrictMono.injective
  apply strictMono_nat_of_lt_succ
  intro j
  have a := hR ⟨0, hr⟩ j
  have b : 2 * c ⟨0, hr⟩ j ≤ (2 * r + 1) ^ (r + 1) * c ⟨0, hr⟩ j := Nat.mul_le_mul_right _ h2
  have := hgt j
  omega
