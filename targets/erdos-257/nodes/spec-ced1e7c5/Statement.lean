import Mathlib
import Nodes.«spec-ced1e7c5».Context

/-- The block step of the Chowla–Erdős method for Erdős 257. Write `f_A(m) = #{a ∈ A : a ∣ m}`
for the binary coefficients of `∑_{a ∈ A} 1/(2^a - 1)` (`Opn.erdos_257_lambert_identity`) and
`T_j = ∑_{i ≥ 1} f_A(j+i)/2^i` for the tail after position `j`. Suppose the sum is the rational
`p/q`. If the weighted block sum `∑_{i=1}^{k} f_A(y+i) 2^(k-i)` of the `k` coefficients after
position `y` is divisible by `2^k` (as it is when every `f_A(y+i)` is divisible by `2^k`, or
when they all vanish), then `q · T_{y+k}` is an integer multiple of `2^k`. Since `q · T_y` is an
integer (`Opn.erdos_257_lambert_tail_integral`) and `T_y = ∑_{i=1}^k f_A(y+i)/2^i + 2^{-k}
T_{y+k}`, the divisibility makes the finite part an integer too. For infinite `A` the tail
`T_{y+k}` is positive, so the multiple is at least `1` and `q · T_{y+k} ≥ 2^k`: this is the
inequality the Chinese-remainder proofs contradict, Erdős 1948 (`f_ℕ = d`, each coefficient
divisible by `2^k`) and Erdős 1968 (pairwise coprime `A`: extra elements dividing `y+k` are
added until the block sum is divisible) by choosing `y` so that the tail after the block is
small on average. In Lean `2^(k-(i+1))` is a natural-number power with `i < k`, so the
subtraction is exact. -/
theorem Opn.erdos_257_block_divisibility :
    ∀ (A : Set ℕ) (p : ℤ) (q : ℕ), 0 < q →
    ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = p / q →
    ∀ y k : ℕ,
      2 ^ k ∣ ∑ i ∈ Finset.range k, Set.ncard {a ∈ A | a ∣ y + i + 1} * 2 ^ (k - (i + 1)) →
      ∃ N : ℤ,
        (q : ℝ) * ∑' i : ℕ, (Set.ncard {a ∈ A | a ∣ y + k + i + 1} : ℝ) / 2 ^ (i + 1) =
          2 ^ k * N := by
  sorry
