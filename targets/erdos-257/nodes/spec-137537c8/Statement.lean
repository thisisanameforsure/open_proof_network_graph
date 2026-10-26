import Mathlib
import Nodes.«spec-137537c8».Context

/-- The Lambert identity for Erdős 257: for every `A ⊆ ℕ`, the sum `∑_{a ∈ A} 1/(2^a - 1)` is the
binary series `∑_{m ≥ 1} f_A(m) / 2^m` whose `m`-th coefficient `f_A(m) = #{a ∈ A : a ∣ m}` counts
the divisors of `m` that lie in `A`. It is the first line of every published irrationality
argument for this problem (Erdős 1948 with `f_ℕ = d`, Erdős 1968, Luca–Tachiya 2014,
Duverney–Tachiya 2019, Tao–Teräväinen with `f = ω`) and of the carry bookkeeping of the
greedy walk. The term at `m = 0` is `0` (the set `{a ∈ A | 0 < m ∧ a ∣ m}` is empty there), and
in Lean a `0 ∈ A` contributes `1/0 = 0` on the left and divides no `m ≥ 1` on the right, so no
hypothesis on `A` is needed. -/
theorem Opn.erdos_257_lambert_identity :
    ∀ (A : Set ℕ),
    ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) =
      ∑' m : ℕ, (Set.ncard {a ∈ A | 0 < m ∧ a ∣ m} : ℝ) / 2 ^ m := by
  sorry
