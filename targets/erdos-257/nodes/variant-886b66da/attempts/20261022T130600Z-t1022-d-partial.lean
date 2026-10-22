import Mathlib
import Nodes.«variant-886b66da».Context

/-- Erdős 257 for every infinite arithmetic progression `A = {a + d n : n ≥ 0}` (`d ≥ 1`).
Known: for `a = 0` this is Erdős 1948 at base `t = 2^d` (J. Indian Math. Soc. 12, 63–66,
Theorem); for `a ≥ 1`, `1/(2^(a+dn) - 1) = 2^(-a)/(t^n + q)` with `t = 2^d` and `q = -2^(-a)`, so
it follows from P. B. Borwein, *On the irrationality of ∑ 1/(q^n + r)*, J. Number Theory 37
(1991), 253–259: `∑_{n ≥ 1} 1/(t^n + q)` is irrational for every integer `t ≥ 2` and rational
`q ∉ {0, -t^n}` (as stated by Kovač–Tao, arXiv:2406.17593, §2.1.2). The even and the odd
integers are the cases `d = 2`. A `0` in `A` contributes `1/0 = 0` in Lean. -/
theorem Opn.erdos_257_arithmetic_progressions :
    ∀ a d : ℕ, 0 < d →
      Irrational (∑' m : {m : ℕ | ∃ n, m = a + d * n}, (1 : ℝ) / (2 ^ m.1 - 1)) := by
  -- approach: an arithmetic progression is an infinite eventually periodic set, so the eventually periodic case (Luca–Tachiya 2014, node variant-5274cf38) gives it at once
  -- licence: CC-BY-4.0
  -- label: eventually periodic sets
  -- claim: $\forall A \subseteq \mathbb{N},\ \bigl(A \text{ infinite} \wedge \exists p \ge 1\ \exists N\ \forall n \ge N,\ (n \in A \iff n + p \in A)\bigr) \Rightarrow \sum_{n \in A} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  -- The statement of node variant-5274cf38, restated as a hole so that this node rests on it.
  have hEP : ∀ A : Set ℕ, A.Infinite →
      (∃ p N : ℕ, 0 < p ∧ ∀ n, N ≤ n → (n ∈ A ↔ n + p ∈ A)) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
    sorry
  intro a d hd
  apply hEP
  · have hinj : Function.Injective (fun n : ℕ => a + d * n) := by
      intro x y hxy
      have : d * x = d * y := by simpa using hxy
      exact Nat.eq_of_mul_eq_mul_left hd this
    exact Set.infinite_of_injective_forall_mem hinj (fun n => ⟨n, rfl⟩)
  · refine ⟨d, a, hd, fun n hn => ?_⟩
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k + 1, by ring⟩
    · rintro ⟨k, hk⟩
      rcases k with _ | k
      · omega
      · exact ⟨k, by rw [mul_add, mul_one] at hk; omega⟩

