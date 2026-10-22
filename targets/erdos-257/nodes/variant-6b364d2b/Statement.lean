import Mathlib
import Nodes.«variant-6b364d2b».Context

/-- Erdős 257 for `A` the set of primes: `∑_p 1/(2^p - 1) = ∑_{n ≥ 1} ω(n)/2^n` is irrational
(this is also Erdős problem 69). Known: T. Tao and J. Teräväinen, *Quantitative correlations and
some problems on prime factors of consecutive integers*, arXiv:2512.01739 (v2, 2026), Theorem 1.3
(§1.3); earlier conditional on a uniform prime tuples conjecture (Pratt 2024). The paper only
sketches the analogous case of the prime powers ("we leave the details … to the interested
reader"), so that case is not stated here. -/
theorem Opn.erdos_257_primes :
    Irrational (∑' p : {p : ℕ | p.Prime}, (1 : ℝ) / (2 ^ p.1 - 1)) := by
  sorry
