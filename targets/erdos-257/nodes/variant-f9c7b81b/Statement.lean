import Mathlib
import Nodes.«variant-f9c7b81b».Context

/-- The set of subset sums of the Mersenne reciprocals, `{Σ_{n∈A} 1/(2^n-1) : A ⊆ ℕ}`, has
Lebesgue measure exactly `1` (the term at `n = 0` is Lean's junk value `0`, so `A` and `A \ {0}`
give the same sum). It is a Cantor set (Kovač–Tao, arXiv:2406.17593, Rem. 4.1: distinct `A` give
distinct sums) of positive measure inside `[0, 1.6067…]`: about 62% of the interval. Erdős 257
asks whether it meets ℚ only in the sums of finite sets; its positive measure is why Kovač
(erdosproblems.com/257) expects the answer to be no. Proof: the sums of sets with prescribed
elements below `N` fill `2^(N-1)` disjoint intervals of length `T_N = Σ_{k≥N} 1/(2^k-1)`
(disjoint by the gap lemma), and `2^(N-1) T_N → 1`. -/
theorem Opn.erdos_257_subsum_set_volume :
    MeasureTheory.volume {x : ℝ | ∃ A : Set ℕ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = x} = 1 := by
  sorry
