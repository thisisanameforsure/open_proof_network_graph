import Mathlib
import Nodes.«variant-c91009b9».Context

/-- Erdős 257 for pairwise coprime `A` with convergent `∑_{n ∈ A} 1/n`. Known: P. Erdős,
*On the irrationality of certain series*, Math. Student 36 (1968), 222–226, Theorem (p. 222:
"Let `(n_i, n_j) = 1`, `∑ 1/n_i < ∞`. Then `∑ 1/(t^{n_i} - 1)` is irrational for every
`t ≥ 2`"; here `t = 2`). Erdős adds that coprimality can be dropped by "more complicated
arguments" whose details he does not give. The primes are pairwise coprime but `∑ 1/p`
diverges, so they are not a case of this statement. -/
theorem Opn.erdos_257_coprime_summable :
    ∀ A : Set ℕ, A.Infinite → A.Pairwise Nat.Coprime →
      Summable (fun n : A => (1 : ℝ) / n.1) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
