import Mathlib
import Nodes.«variant-77c0756e».Context

/-- Erdős 257 for the union of two fast divisibility chains. Let `x` and `y` be sequences of
positive integers in which each term divides the next and is at most a third of it
(`x j ∣ x (j+1)` and `3 x j ≤ x (j+1)`, the same for `y`). Then
`∑_{n ∈ range x ∪ range y} 1/(2^n - 1)` is irrational. Examples: the powers of any two bases
`a, b ≥ 3`, or `{3^k} ∪ {(3k)!}`, or `{2·3^k} ∪ {5^k}`. Such a union need not be lacunary of
ratio two, and the elements below an element need not sum to less than it, so neither
`Opn.erdos_257_eventually_ratio_two` nor `Opn.erdos_257_long_gaps` applies. The proof uses
Liouville's criterion (`Opn.erdos_257_liouville_criterion`): below `m` the partial sum has the
common denominator `(2^(x J) - 1)(2^(y K) - 1)`, with `x J` and `y K` the largest chain elements
below `m`. Put `Z = y (K+1)` and let `x J` be the largest `x`-element with `x J ≤ Z`. Either
`m = Z` leaves margin `Z - y K - x J ≥ C`, or `x J > Z - y K - C`, and then
`m = min (x (J+1)) (y (K+2))` leaves margin at least `C`, because `x (J+1) ≥ 3 x J` and
`Z ≥ 3 y K`. The proof is elementary and complete. -/
theorem Opn.erdos_257_two_chains :
    ∀ x y : ℕ → ℕ, 0 < x 0 → 0 < y 0 →
    (∀ j, x j ∣ x (j + 1)) → (∀ j, y j ∣ y (j + 1)) →
    (∀ j, 3 * x j ≤ x (j + 1)) → (∀ j, 3 * y j ≤ y (j + 1)) →
    Irrational (∑' n : (Set.range x ∪ Set.range y : Set ℕ), (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry
