import Mathlib
import Nodes.«spec-2e765953».Context

/-- The prime-indexed Lambert series of the root's identity converges: the sum over primes `p`
of `1 / (2 ^ p - 1)` is summable in ℝ. This is the right-hand side of `erdos-69--h1-v2`. -/
theorem Opn.erdos_69_summable_prime_reciprocal :
    Summable (fun p : Nat.Primes => (1 : ℝ) / (2 ^ (p : ℕ) - 1)) := by
  sorry
