open Finset
open Erdos774

/-! Non-vacuity witness (D-4 step 7): the powers of two form an infinite set every finite subset of which is dissociated (subset sums of distinct powers of two are distinct, by their binary digits), so it is proportionately dissociated with constant c = 1. -/

theorem witness : ∃ (A : Set ℕ), A.Infinite ∧ A.IsProportionatelyDissociated := by
  have hinj : Function.Injective (fun i : ℕ => 2 ^ i) := Nat.pow_right_injective le_rfl
  have key : ∀ (U : Finset ℕ), (↑U : Set ℕ) ⊆ Set.range (fun i : ℕ => 2 ^ i) →
      U = (U.image (Nat.log 2)).image (fun i : ℕ => 2 ^ i) := by
    intro U hU
    ext n
    simp only [Finset.mem_image, exists_exists_and_eq_and]
    constructor
    · intro hn
      obtain ⟨i, rfl⟩ := hU hn
      exact ⟨2 ^ i, hn, by rw [Nat.log_pow one_lt_two]⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨i, rfl⟩ := hU hm
      rwa [Nat.log_pow one_lt_two]
  have hsum : ∀ (U : Finset ℕ), (↑U : Set ℕ) ⊆ Set.range (fun i : ℕ => 2 ^ i) →
      ∑ n ∈ U, n = ∑ i ∈ U.image (Nat.log 2), 2 ^ i := by
    intro U hU
    conv_lhs => rw [key U hU]
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
  refine ⟨Set.range (fun i : ℕ => 2 ^ i), Set.infinite_range_of_injective hinj, 1, one_pos,
    fun B hB => ⟨B, Finset.Subset.refl B, by simp, ?_⟩⟩
  intro S hS S' hS' h
  have hSB : (↑S : Set ℕ) ⊆ Set.range (fun i : ℕ => 2 ^ i) := Set.Subset.trans hS hB
  have hS'B : (↑S' : Set ℕ) ⊆ Set.range (fun i : ℕ => 2 ^ i) := Set.Subset.trans hS' hB
  have hT : S.image (Nat.log 2) = S'.image (Nat.log 2) := by
    have h3 : ∑ i ∈ S.image (Nat.log 2), 2 ^ i = ∑ i ∈ S'.image (Nat.log 2), 2 ^ i :=
      ((hsum S hSB).symm.trans h).trans (hsum S' hS'B)
    have h4 := congrArg (fun n => n.bitIndices.toFinset) h3
    simpa only [Finset.toFinset_bitIndices_twoPowSum] using h4
  rw [key S hSB, key S' hS'B, hT]

