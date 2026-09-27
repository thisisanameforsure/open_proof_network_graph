import Mathlib
import Nodes.«variant-b89de5c4».Context

/-! Graham's gcd conjecture (Erdős problem 402) for eighteen-element sets. With M the largest
element, if gcd(M, x) > M/18 for every x then every other x is (j/k)M with j < k ≤ 17, so
L·x/M (L = lcm(1..17) = 12252240) lies in a fixed set S of 95 values. S splits into 16 classes in
each of which any two distinct values c, d have 18·gcd(c, d) ≤ c or ≤ d; by pigeonhole two of
the 17 other elements share a class, and gcd(x, y)·L = gcd(c, d)·M transfers the bound. -/

theorem Opn.erdos_402_card_eighteen :
    ∀ (A : Finset ℕ), 0 ∉ A → A.card = 18 → ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
