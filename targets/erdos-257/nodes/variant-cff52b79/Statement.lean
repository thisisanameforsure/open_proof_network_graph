import Mathlib
import Nodes.«variant-cff52b79».Context

/-- A counterexample's complement is never a counterexample: for every set `A` of natural
numbers, `∑_{n ∈ A} 1/(2^n - 1)` or `∑_{n ∉ A} 1/(2^n - 1)` is irrational. The two sums add up to
the Erdős–Borwein constant `∑_{n ≥ 1} 1/(2^n - 1)`, which is irrational (Erdős 1948, node
variant-2f5236aa), and two rationals cannot add up to an irrational. On the Cantor set of all
subset sums, complement is the reflection `x ↦ c - x` about half that constant, so the
reflection sends every rational point of the set to an irrational one. For finite `A` this is
Erdős's theorem again (the complement is cofinite); for infinite `A` with infinite complement it
says that `A` and `ℕ \ A` are never both counterexamples to Erdős 257. At `n = 0` the term is
Lean's junk value `0`, so whether `0` lies in `A` changes neither sum. -/
theorem Opn.erdos_257_compl :
    ∀ (A : Set ℕ),
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) ∨
      Irrational (∑' n : ↥Aᶜ, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
