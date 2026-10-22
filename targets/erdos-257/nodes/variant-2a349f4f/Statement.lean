import Mathlib
import Nodes.«variant-2a349f4f».Context

/-- The subset sums of the Mersenne reciprocals, `{Σ_{n∈A} 1/(2^n-1) : A ⊆ ℕ}`, form a Cantor
set: compact, perfect (no isolated points) and with empty interior, hence nowhere dense and,
being a closed subset of ℝ with empty interior, totally disconnected. This is the topological
half of Kovač–Tao (arXiv:2406.17593, Rem. 4.1); the set's Lebesgue measure is exactly `1`
(node variant-f9c7b81b), so it is a "fat" Cantor set. Proof: the set is the continuous image of
Cantor space; flipping one far digit moves a sum by `1/(2^n-1)`, so no point is isolated; and every
interval meeting the set contains one of its gaps `(s + T_{N+1}, s + 1/(2^N-1))`, kept empty
by the gap lemma. -/
theorem Opn.erdos_257_subsum_set_cantor :
    IsCompact {x : ℝ | ∃ A : Set ℕ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = x} ∧
      Perfect {x : ℝ | ∃ A : Set ℕ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = x} ∧
      interior {x : ℝ | ∃ A : Set ℕ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = x} = ∅ := by
  sorry
