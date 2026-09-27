import Mathlib
import Nodes.«variant-09e95e7a».Context

/-! A related variant of Erdős problem 69 (D-30, relation `related`): the binary number whose
n-th digit is 1 exactly when n is prime, `∑_{p prime} 2^{-p}`, is irrational.

Why it sits beside erdos-69: the root's standing decomposition (erdos-69--h2-v2 and below) turns
rationality of `∑ ω(n)/2^n` into "b times every tail `∑_{j≥1} ω(N+j)/2^j` is an integer" and is
blocked on controlling ω on a window of consecutive integers. For the prime indicator the same
tail argument closes, because the window is controllable: `(k+1)! + 2, …, (k+1)! + k + 1` are
all composite, so the tail after `N = (k+1)! + 1` lies strictly between 0 and `2^{-k}`. This
node is a worked, gate-checked instance of the method, not progress on the root. -/

theorem Opn.erdos_69_prime_indicator :
    Irrational (∑' n : ℕ, if n.Prime then (1 / 2 : ℝ) ^ n else 0) := by
  sorry
