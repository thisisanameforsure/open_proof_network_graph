import Mathlib
import Nodes.«spec-689ac1ac».Context

/-- The divisible-block step of the Chowla–Erdős method for Erdős 257. Write
`f_A(m) = #{a ∈ A : a ∣ m}` for the binary coefficients of `∑_{a ∈ A} 1/(2^a - 1)`
(`Opn.erdos_257_lambert_identity`) and `T_j = ∑_{i ≥ 1} f_A(j+i)/2^i` for the tail after
position `j`. Suppose the sum is the rational `p/q`. If the `k` coefficients after position `y`,
`f_A(y+1), …, f_A(y+k)`, are all divisible by `2^k` (a block of zeros is the case they all
vanish), then `q · T_{y+k}` is an integer multiple of `2^k`. Since `q · T_y` is an integer
(`Opn.erdos_257_lambert_tail_integral`) and `T_y = ∑_{i=1}^k f_A(y+i)/2^i + 2^{-k} T_{y+k}`,
the divisibility makes the finite part an integer too. For infinite `A` the tail `T_{y+k}` is
positive, so the multiple is at least `1` and `q · T_{y+k} ≥ 2^k`: this is the inequality every
Chinese-remainder proof (Erdős 1948 with `f_ℕ = d`, Duverney–Tachiya 2019) contradicts by
choosing `y` so that the tail after the block is small on average. -/
theorem Opn.erdos_257_divisible_block :
    ∀ (A : Set ℕ) (p : ℤ) (q : ℕ), 0 < q →
    ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = p / q →
    ∀ y k : ℕ, (∀ i, 1 ≤ i → i ≤ k → 2 ^ k ∣ Set.ncard {a ∈ A | a ∣ y + i}) →
      ∃ N : ℤ,
        (q : ℝ) * ∑' i : ℕ, (Set.ncard {a ∈ A | a ∣ y + k + i + 1} : ℝ) / 2 ^ (i + 1) =
          2 ^ k * N := by
  sorry
