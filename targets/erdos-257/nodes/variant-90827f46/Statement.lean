import Mathlib
import Nodes.«variant-90827f46».Context

/-- Erdős 257 for a union of finitely many lacunary sequences. Let `c 0, …, c (r-1)` be `r ≥ 1`
sequences of positive integers, each growing by a factor of at least `(2r+1)^(r+1)` from one
term to the next (no divisibility and no relation between the sequences is assumed). Then
`∑_{n ∈ A} 1/(2^n - 1)` is irrational for `A` the union of their ranges. For `r = 1` the
factor is 9 (a case `Opn.erdos_257_eventually_ratio_two` already covers); for three sequences
it is `7^4 = 2401`, met for instance by `n ↦ 2401^n`, `n ↦ 3·2401^n` and
`n ↦ (n + 1)·2401^n`, the last not a divisibility chain. The union need not be lacunary of ratio two,
so `Opn.erdos_257_eventually_ratio_two` does not apply, and the sequences need not be
divisibility chains, as `Opn.erdos_257_two_chains` requires. Proof: by pigeonhole over the
`r + 1` windows `(q^k T, q^(k+1) T]`, `q = 2r+1`, `k = 0, …, r`, one window contains no
element of `A`, because two elements of one sequence in `(T, q^(r+1) T]` would contradict its
growth. The least element `m` of `A` above `q^k T` then exceeds `(2r+1) q^k T`, while the
elements of each sequence below `m` are at most `q^k T` and sum to at most twice that. So `m`
exceeds the sum of all smaller elements of `A` by at least `T`, and Liouville's criterion
(`Opn.erdos_257_liouville_criterion`, common denominator `∏_{a ∈ A, a < m} (2^a - 1)`)
applies, as in `Opn.erdos_257_long_gaps`. The proof is elementary and complete. -/
theorem Opn.erdos_257_lacunary_union :
    ∀ (r : ℕ) (c : Fin r → ℕ → ℕ), 0 < r → (∀ i, 0 < c i 0) →
    (∀ i j, (2 * r + 1) ^ (r + 1) * c i j ≤ c i (j + 1)) →
    Irrational (∑' n : (⋃ i, Set.range (c i) : Set ℕ), (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
