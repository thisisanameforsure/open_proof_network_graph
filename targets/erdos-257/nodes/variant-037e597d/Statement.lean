import Mathlib
import Nodes.«variant-037e597d».Context

/-- Erdős 257 for the powers of two together with the powers of three:
`∑_{n ∈ {2^k} ∪ {3^k}} 1/(2^n - 1)` is irrational. The set is not lacunary of ratio two
(`2^k < 3^j < 2^(k+1)` happens infinitely often), so `Opn.erdos_257_eventually_ratio_two` does
not apply, but Liouville's criterion (`Opn.erdos_257_liouville_criterion`) does. Each part is a
divisibility chain, so below `m` the common denominator of the partial sum is
`(2^(2^k) - 1)(2^(3^J) - 1)`, with `2^k` and `3^J` the largest powers below `m`; taking
`m = min(2^(k+1), 3^(J+1))`, it suffices that some power `2^k` lies in `[3^J + C, 2·3^J - C]`.
If that failed for both `J` and `J + 1`, both `3^J` and `3^(J+1)` would lie within `C` of a power
of two, `2^x` and `2^y`, and then `|2^y - 3·2^x| < 4C`. But `|2^y - 3·2^x| ≥ 2^x`, because
`2^d ≠ 3`. That is impossible once `3^J ≥ 5C + 1`. The reciprocals of the set are
summable, so the result is covered in principle by Erdős's remark (Math. Student 36, 1968) that
coprimality can be dropped from his 1968 theorem; the proof here is elementary and complete. -/
theorem Opn.erdos_257_powers_of_two_and_three :
    Irrational (∑' n : ({n | ∃ k : ℕ, n = 2 ^ k} ∪ {n | ∃ k : ℕ, n = 3 ^ k} : Set ℕ),
      (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
