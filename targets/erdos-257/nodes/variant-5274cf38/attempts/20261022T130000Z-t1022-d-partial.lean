import Mathlib
import Nodes.«variant-5274cf38».Context

/-- Erdős 257 for every infinite `A` whose indicator is eventually periodic (for example any
arithmetic progression, the odd numbers, any union of residue classes, changed in finitely many
places). Known: F. Luca and Y. Tachiya, *Irrationality of Lambert series associated with a
periodic sequence*, Int. J. Number Theory 10 (2014), 623–636, Theorem 1.1 (restated as Theorem A,
RIMS Kôkyûroku 2014 (2017), p. 139): `∑ a(n)/(q^n - 1)` is irrational for every purely periodic
integer sequence `a`, not identically zero, and every integer `|q| > 1`. An eventually periodic
infinite `A` differs from a nonempty purely periodic set in finitely many places, which changes
the sum by a rational number. -/
theorem Opn.erdos_257_eventually_periodic :
    ∀ A : Set ℕ, A.Infinite →
      (∃ p N : ℕ, 0 < p ∧ ∀ n, N ≤ n → (n ∈ A ↔ n + p ∈ A)) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  -- approach: shift an eventually periodic set to a purely periodic one that differs from it in finitely many places; the finite difference is rational, leaving exactly the purely periodic case proved by Luca and Tachiya (IJNT 2014, Theorem 1.1)
  -- licence: CC-BY-4.0
  -- label: purely periodic sets (Luca–Tachiya)
  -- claim: $\forall B \subseteq \mathbb{N},\ \bigl(B \neq \emptyset \wedge \exists p \ge 1\ \forall n,\ (n \in B \iff n + p \in B)\bigr) \Rightarrow \sum_{n \in B} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  -- This is Luca–Tachiya's Theorem 1.1 for the 0/1 sequence a(n) = 1_B(n) at q = 2 (an element 0 of B contributes 1/0 = 0 in Lean).
  have hper : ∀ B : Set ℕ, B.Nonempty → (∃ p : ℕ, 0 < p ∧ ∀ n, n ∈ B ↔ n + p ∈ B) →
      Irrational (∑' n : B, (1 : ℝ) / (2 ^ n.1 - 1)) := by
    sorry
  intro A hA ⟨p, N, hp, hAper⟩
  classical
  set f : ℕ → ℝ := fun n => (1 : ℝ) / (2 ^ n - 1) with hf
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) (fun n => ?_) (fun n => ?_)
      ((summable_geometric_two).mul_left 2)
    · have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      exact div_nonneg zero_le_one (by linarith)
    · rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [hf]
      · have h2 : (2 : ℝ) ≤ 2 ^ n := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
        have hpos : (0 : ℝ) < 2 ^ n - 1 := by linarith
        simp only [hf]
        rw [div_le_iff₀ hpos, one_div_pow, mul_assoc, mul_comm ((1:ℝ) / 2 ^ n), mul_one_div,
          mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith
  have hiter : ∀ k n, N ≤ n → (n ∈ A ↔ n + p * k ∈ A) := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [ih n hn, hAper (n + p * k) (by omega)]
      rw [show n + p * k + p = n + p * (k + 1) by ring]
  let B : Set ℕ := {n | n + p * N ∈ A}
  have hpN : N ≤ p * N := Nat.le_mul_of_pos_left N hp
  have hBper : ∀ n, n ∈ B ↔ n + p ∈ B := by
    intro n
    show n + p * N ∈ A ↔ n + p + p * N ∈ A
    rw [hAper (n + p * N) (by omega), show n + p * N + p = n + p + p * N by ring]
  have hAB : ∀ n, N ≤ n → (n ∈ A ↔ n ∈ B) := fun n hn => hiter N n hn
  have hBne : B.Nonempty := by
    obtain ⟨m, hm, hmN⟩ := hA.exists_gt N
    exact ⟨m, (hAB m hmN.le).1 hm⟩
  have hB := hper B hBne ⟨p, hp, hBper⟩
  have h1 := hfs.indicator A
  have h2 := hfs.indicator B
  have hsub := h1.tsum_sub h2
  have hfin : ∑' n, (A.indicator f n - B.indicator f n) =
      ∑ n ∈ Finset.range N, (A.indicator f n - B.indicator f n) := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp only [Set.indicator_apply]
    by_cases hnA : n ∈ A
    · simp [hnA, (hAB n hn).1 hnA]
    · have : n ∉ B := fun h => hnA ((hAB n hn).2 h)
      simp [hnA, this]
  have hrat : ∑ n ∈ Finset.range N, (A.indicator f n - B.indicator f n) =
      ((∑ n ∈ Finset.range N, ((if n ∈ A then (1 : ℚ) / (2 ^ n - 1) else 0) -
        (if n ∈ B then (1 : ℚ) / (2 ^ n - 1) else 0)) : ℚ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [Set.indicator_apply, hf]
    split_ifs <;> push_cast <;> ring
  have key : ∑' n : A, f n = ∑' n : B, f n + ((∑ n ∈ Finset.range N,
      ((if n ∈ A then (1 : ℚ) / (2 ^ n - 1) else 0) -
        (if n ∈ B then (1 : ℚ) / (2 ^ n - 1) else 0)) : ℚ) : ℝ) := by
    rw [tsum_subtype A f, tsum_subtype B f, ← hrat, ← hfin, hsub]
    ring
  obtain ⟨q, hq⟩ : ∃ q : ℚ, ∑' n : A, f n = ∑' n : B, f n + (q : ℝ) := ⟨_, key⟩
  show Irrational (∑' n : A, f n)
  rw [hq]
  rintro ⟨r, hr⟩
  exact hB ⟨r - q, by push_cast; linarith⟩

