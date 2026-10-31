import Mathlib
import Nodes.«variant-cce9b284».Context

/-- The refutation side of Erdős 257 stated as one existential: the Mersenne reciprocal sum of
some infinite set `A ⊆ ℕ` is a rational number. Any construction of a counterexample is a route
to this statement, whether it names its rational (`1/2`, the sibling variant) or settles on one
it does not name, as the repair walk below does. -/
theorem Opn.erdos_257_some_infinite_sum_is_rational :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ s : ℚ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = s := by
  -- approach: repair walk: greedy walk of a rational x in the terms 1/(2^m-1); when a chosen term leaves the remainder beyond the whole tail, subtract the next term from the target and go on; the chosen set sums to x minus the subtracted terms, a counterexample once that subtracted sum is rational
  -- licence: CC-BY-4.0
  have hall :
      (∀ (x : ℚ) (r : ℕ → ℝ) (q : ℕ → ℕ), 0 ≤ x → r 0 = x →
        (∀ m : ℕ, q m = ⌊r m / ((1 : ℝ) / (2 ^ m - 1))⌋₊ ∧
          r (m + 1) = r m - q m * ((1 : ℝ) / (2 ^ m - 1))) →
        ∑' n : {m : ℕ | q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1)},
            (1 : ℝ) / (2 ^ n.1 - 1) =
          x - ∑' m : ℕ, ((q m : ℝ) -
            if q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1) then 1 else 0) *
              ((1 : ℝ) / (2 ^ m - 1))) ∧
      (∃ (x : ℚ) (r : ℕ → ℝ) (q : ℕ → ℕ), 0 < x ∧ r 0 = x ∧
        (∀ m : ℕ, q m = ⌊r m / ((1 : ℝ) / (2 ^ m - 1))⌋₊ ∧
          r (m + 1) = r m - q m * ((1 : ℝ) / (2 ^ m - 1))) ∧
        {m : ℕ | q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1)}.Infinite ∧
        ∃ s : ℚ, ∑' m : ℕ, ((q m : ℝ) -
            if q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1) then 1 else 0) *
              ((1 : ℝ) / (2 ^ m - 1)) = s) := by
    refine ⟨?_, ?_⟩
    ·
      -- label: the walk accounts for x
      -- claim: $\sum_{m\in A}\frac{1}{2^m-1}=x-\sum_{m}\bigl(q_m-\mathbf 1_A(m)\bigr)\frac{1}{2^m-1}$
      -- The walk from a rational x ≥ 0: r_0 = x, q_m = ⌊r_m (2^m - 1)⌋ counts how many times the
      -- term 1/(2^m - 1) is subtracted at index m, and r_{m+1} = r_m - q_m/(2^m - 1) is the
      -- remainder carried to the next index. A is the set of indices whose last subtraction
      -- leaves the remainder within the tail Σ_{j>m} 1/(2^j - 1), the chosen terms; every other
      -- subtraction is a repair. The chosen sum is x less the repair sum.
      have h_account : ∀ (x : ℚ) (r : ℕ → ℝ) (q : ℕ → ℕ), 0 ≤ x → r 0 = x →
          (∀ m : ℕ, q m = ⌊r m / ((1 : ℝ) / (2 ^ m - 1))⌋₊ ∧
            r (m + 1) = r m - q m * ((1 : ℝ) / (2 ^ m - 1))) →
          ∑' n : {m : ℕ | q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1)},
              (1 : ℝ) / (2 ^ n.1 - 1) =
            x - ∑' m : ℕ, ((q m : ℝ) -
              if q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1) then 1 else 0) *
                ((1 : ℝ) / (2 ^ m - 1)) := by
        sorry
      exact h_account
    ·
      -- label: a rational whose repair sum is rational
      -- claim: $\exists x\in\mathbb{Q}_{>0}:\ A(x)\ \text{infinite}\ \wedge\ \sum_{m}\bigl(q_m-\mathbf 1_{A(x)}(m)\bigr)\frac{1}{2^m-1}\in\mathbb{Q}$
      -- Some positive rational x whose walk (r_0 = x, q_m = ⌊r_m (2^m - 1)⌋,
      -- r_{m+1} = r_m - q_m/(2^m - 1)) chooses infinitely many indices and whose repair sum, the
      -- subtracted terms counted with multiplicity, is a rational number. Two ways to meet it:
      -- only finitely many repairs, or infinitely many whose sum is rational all the same.
      have h_walk : ∃ (x : ℚ) (r : ℕ → ℝ) (q : ℕ → ℕ), 0 < x ∧ r 0 = x ∧
          (∀ m : ℕ, q m = ⌊r m / ((1 : ℝ) / (2 ^ m - 1))⌋₊ ∧
            r (m + 1) = r m - q m * ((1 : ℝ) / (2 ^ m - 1))) ∧
          {m : ℕ | q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1)}.Infinite ∧
          ∃ s : ℚ, ∑' m : ℕ, ((q m : ℝ) -
              if q m ≠ 0 ∧ r (m + 1) ≤ ∑' j : ℕ, (1 : ℝ) / (2 ^ (m + 1 + j) - 1) then 1 else 0) *
                ((1 : ℝ) / (2 ^ m - 1)) = s := by
        sorry
      exact h_walk
  obtain ⟨h_account, h_walk⟩ := hall
  obtain ⟨x, r, q, hx, h0, hrec, hA, s, hs⟩ := h_walk
  refine ⟨_, hA, x - s, ?_⟩
  rw [h_account x r q hx.le h0 hrec, hs]
  push_cast
  ring
