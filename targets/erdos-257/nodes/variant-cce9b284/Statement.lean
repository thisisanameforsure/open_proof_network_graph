import Mathlib
import Nodes.«variant-cce9b284».Context

/-- The refutation side of Erdős 257 stated as one existential: the Mersenne reciprocal sum of
some infinite set `A ⊆ ℕ` is a rational number. Any construction of a counterexample is a route
to this statement, whether it names its rational (`1/2`, the sibling variant) or settles on one
it does not name, as the repair walk below does. -/
theorem Opn.erdos_257_some_infinite_sum_is_rational :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ s : ℚ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = s := by
  sorry
