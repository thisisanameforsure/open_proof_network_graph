import Mathlib

/-! Declared dependencies (D-4 step 8): `spec-23b0fff0`. -/

/-- Integrality of the binary tails, the second line of every digit-method proof for Erdős 257
(Erdős 1948 and 1968, Duverney–Tachiya 2019). Write `f_A(m) = #{a ∈ A : a ∣ m}` for the
coefficients of the binary expansion `∑_{a ∈ A} 1/(2^a - 1) = ∑_{m ≥ 1} f_A(m)/2^m`
(`Opn.erdos_257_lambert_identity`) and `T_j = ∑_{i ≥ 1} f_A(j+i)/2^i` for the tail after
position `j`, scaled by `2^j`. If the sum is the rational `p/q` then, for every `j`,
`q · T_j = p · 2^j - q · ∑_{m ≤ j} f_A(m) 2^(j-m)`, an integer. Every proof of a special case
then shows that for a well-chosen `j` this integer cannot exist: it is positive whenever some
element of `A` exceeds `j` (so `T_j ≥ 1/q`), while a block of coefficients `f_A(j+1), …,
f_A(j+k)` that vanish, or are divisible by `2^k`, forces `q · T_{j+k} ≥ 2^k` against an upper
bound on that tail. In Lean `2^(j-m)` is a natural-number power with `m ≤ j`, so the subtraction
is exact, and `f_A(0) = 0` by the guard `0 < m`. -/
theorem Opn.erdos_257_lambert_tail_integral :
    ∀ (A : Set ℕ) (p : ℤ) (q : ℕ), 0 < q →
    ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = p / q →
    ∀ j : ℕ,
      (q : ℝ) * ∑' i : ℕ, (Set.ncard {a ∈ A | a ∣ j + i + 1} : ℝ) / 2 ^ (i + 1) =
        ((p * 2 ^ j -
          q * ∑ m ∈ Finset.range (j + 1), (Set.ncard {a ∈ A | 0 < m ∧ a ∣ m} : ℤ) * 2 ^ (j - m)
          : ℤ) : ℝ) := by
  sorry
