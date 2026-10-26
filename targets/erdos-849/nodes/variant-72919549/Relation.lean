-- relation: partial
import Mathlib

theorem relation :
    (∀ t ≥ 1, ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = a}.ncard = t) →
      ∀ N : ℕ, ∃ a ≥ N, 3 ≤ {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = a}.ncard := by
  intro h N
  by_contra hc
  push_neg at hc
  have h' : ∀ t : ℕ, ∃ a : ℕ,
      {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = a}.ncard = t + 3 :=
    fun t => h (t + 3) (by omega)
  choose f hf using h'
  have hlt : ∀ t, f t < N := by
    intro t
    by_contra hle
    push_neg at hle
    have := hc (f t) hle
    rw [hf t] at this
    omega
  obtain ⟨x, _, y, _, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (N + 1)) (t := Finset.range N) (f := f) (by simp)
    (fun t _ => Finset.mem_range.mpr (hlt t))
  have := hf x
  rw [heq, hf y] at this
  omega
