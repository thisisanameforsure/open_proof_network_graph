import Mathlib
import Nodes.«variant-293c7f51».Context

open Nat

private theorem choose_mono_half {n r : ℕ} :
    ∀ j, r ≤ j → j ≤ n / 2 → n.choose r ≤ n.choose j := by
  intro j
  induction j with
  | zero => intro h _; rw [Nat.le_zero.mp h]
  | succ j ih =>
    intro hr hj
    rcases Nat.eq_or_lt_of_le hr with h | h
    · rw [h]
    · exact (ih (by omega) (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem sol_set_eq (a B : ℕ) (ha : 2 ≤ a) (hB : a < (B + 1).choose 2) :
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a} =
      ↑(insert a ((Finset.range (B + 1)).filter
        (fun n => ((Finset.Icc 1 (n / 2)).filter (fun k => choose n k = a)).Nonempty))) := by
  ext n
  simp only [Set.mem_setOf_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_filter,
    Finset.mem_range, Finset.filter_nonempty_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hk1, hk2, h⟩
    by_cases hn : n ≤ B
    · right
      exact ⟨by omega, k, ⟨hk1, by omega⟩, h⟩
    · left
      by_cases hk : k = 1
      · subst hk; simpa using h
      · exfalso
        have h2 : n.choose 2 ≤ n.choose k := choose_mono_half k (by omega) (by omega)
        have h3 : (B + 1).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 (by omega)
        omega
  · rintro (rfl | ⟨_, k, ⟨hk1, hk2⟩, h⟩)
    · exact ⟨1, le_rfl, by omega, by simp⟩
    · exact ⟨k, hk1, by omega, h⟩

/-- Erdős 849 for $t = 3$: some integer $a$ is $\binom{n}{k}$ with $1 \le k \le n/2$ in exactly
3 rows $n$. The proof takes $a = 120$: rows 10, 16 and 120 ($\binom{10}{3}=\binom{16}{2}=\binom{120}{1}$). -/
theorem Opn.erdos_849_t3 :
    ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 3 := by
  refine ⟨120, ?_⟩
  rw [sol_set_eq 120 16 (by norm_num) (by decide), Set.ncard_coe_finset]
  decide
