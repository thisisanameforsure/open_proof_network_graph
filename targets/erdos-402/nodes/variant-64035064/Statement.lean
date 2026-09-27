import Mathlib
import Nodes.«variant-64035064».Context

/-! Graham's gcd conjecture (Erdős problem 402) for sixteen-element sets. With M the largest
element, if gcd(M, x) > M/16 for every x then every other x is (j/k)M with j < k ≤ 15, so
L·x/M (L = lcm(1..15) = 360360) lies in a fixed set S of 71 values. S splits into 14 classes in
each of which any two distinct values c, d have 16·gcd(c, d) ≤ c or ≤ d; by pigeonhole two of
the 15 other elements share a class, and gcd(x, y)·L = gcd(c, d)·M transfers the bound. -/

theorem Opn.erdos_402_card_sixteen :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 16 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
