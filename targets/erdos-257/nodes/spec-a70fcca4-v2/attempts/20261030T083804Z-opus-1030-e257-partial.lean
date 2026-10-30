import Mathlib
import Nodes.«spec-a70fcca4-v2».Context

/-- The natural counterexample candidate for Erdős 257, stated so that it can be proved or
refuted: `1/2` is the Mersenne reciprocal sum of some infinite set. A finite set cannot give
`1/2` (finite sums have odd denominators), so any representation of `1/2` is infinite, and a
proof of this statement refutes the root. The greedy walk for `1/2` (the only possible
representation) begins 2, 3, 6, 7, 14, 20, 21, 26, 27, 32, ... and has been run without stalling
to depth 2500 here and to depth 10^8 by Hong (Zenodo 23287959, 2026, unrefereed); Kovač
(erdosproblems.com/257, Aug 2025) expects the subset-sum set, a fat Cantor set, to contain
such rationals. No proof in either direction is known. -/
theorem Opn.erdos_257_half_is_a_subsum :
    ∃ A : Set ℕ, A.Infinite ∧ ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = 1 / 2 := by
  -- approach: carry form: 1/2 is a subset sum once an infinite set keeps its integer carries between 0 and a linear bound
  -- licence: CC-BY-4.0
  -- label: Lambert identity
  -- claim: $\sum_{n\in A}\frac{1}{2^n-1}=\sum_{m\ge 1}\frac{\#\{a\in A:\ a\mid m\}}{2^m}$
  -- The Mersenne sum of A, rewritten as a binary expansion whose m-th coefficient counts the
  -- elements of A dividing m (the statement of node spec-137537c8).
  have h_lambert : ∀ (A : Set ℕ),
      ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) =
        ∑' m : ℕ, (Set.ncard {a ∈ A | 0 < m ∧ a ∣ m} : ℝ) / 2 ^ m := by
    sorry
  -- label: carry criterion
  -- claim: $0\le Z_j\le C(j+1)\ \forall j\ \Rightarrow\ \sum_{m}\frac{d_A(m)}{2^m}=\frac{p}{q}$
  -- Here d_A(m) counts the elements of A dividing m, and the carry is the integer
  -- Z_j = p 2^j - q (d_A(1) 2^(j-1) + ... + d_A(j)), which satisfies Z_(j+1) = 2 Z_j - q d_A(j+1).
  -- If every carry is nonnegative and they grow at most linearly, the expansion sums to p/q.
  have h_crit : ∀ (A : Set ℕ) (p : ℤ) (q : ℕ), 0 < q →
      (∀ j : ℕ, (0 : ℤ) ≤ p * (2 : ℤ) ^ j - (q : ℤ) *
        ∑ m ∈ Finset.range (j + 1), ((Set.ncard {a ∈ A | 0 < m ∧ a ∣ m} : ℕ) : ℤ) * (2 : ℤ) ^ (j - m)) →
      (∃ C : ℤ, ∀ j : ℕ, p * (2 : ℤ) ^ j - (q : ℤ) *
        ∑ m ∈ Finset.range (j + 1), ((Set.ncard {a ∈ A | 0 < m ∧ a ∣ m} : ℕ) : ℤ) * (2 : ℤ) ^ (j - m)
          ≤ C * ((j : ℤ) + 1)) →
      ∑' m : ℕ, (Set.ncard {a ∈ A | 0 < m ∧ a ∣ m} : ℝ) / 2 ^ m = p / q := by
    sorry
  -- label: pre-charged carries for 1/2
  -- claim: $\exists A\ \text{infinite}:\ 0\le 2^j-2\sum_{m\le j}d_A(m)\,2^{j-m}\le C(j+1)\ \forall j$
  -- Some infinite set A has carries for the target 1/2 (p = 1, q = 2) that stay nonnegative
  -- and at most linear, where d_A(m) counts the elements of A dividing m.
  have h_carry : ∃ A : Set ℕ, A.Infinite ∧
      (∀ j : ℕ, (0 : ℤ) ≤ (2 : ℤ) ^ j - 2 *
        ∑ m ∈ Finset.range (j + 1), ((Set.ncard {a ∈ A | 0 < m ∧ a ∣ m} : ℕ) : ℤ) * (2 : ℤ) ^ (j - m)) ∧
      ∃ C : ℤ, ∀ j : ℕ, (2 : ℤ) ^ j - 2 *
        ∑ m ∈ Finset.range (j + 1), ((Set.ncard {a ∈ A | 0 < m ∧ a ∣ m} : ℕ) : ℤ) * (2 : ℤ) ^ (j - m)
          ≤ C * ((j : ℤ) + 1) := by
    sorry
  obtain ⟨A, hA, hz, C, hC⟩ := h_carry
  refine ⟨A, hA, ?_⟩
  have hsum := h_crit A 1 2 (by norm_num) (fun j => by simpa using hz j) ⟨C, fun j => by simpa using hC j⟩
  rw [h_lambert A, hsum]
  norm_num
