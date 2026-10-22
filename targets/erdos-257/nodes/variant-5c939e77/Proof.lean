import Mathlib
import Nodes.«variant-5c939e77».Context

/-- Only countably many sets of positive integers have a rational Mersenne reciprocal sum, so
Erdős 257 has at most countably many counterexamples. This is the "immediate consequence" that
Kovač and Tao draw from the distinctness of the subset sums (V. Kovač and T. Tao, *On several
irrationality problems for Ahmes series*, arXiv:2406.17593 v4, §2.1.2 p. 4 and Remark 4.1
p. 13; Acta Math. Hungar. 175 (2025)). Finite sets are included: every finite set has a
rational sum, and the statement says the whole family is still countable. It follows from
uniqueness of representation (`spec-5e2e0890`) because the rationals are countable. -/
theorem Opn.erdos_257_rational_subsums_countable :
    {A : Set ℕ | 0 ∉ A ∧ ∃ q : ℚ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = q}.Countable := by
  refine Set.MapsTo.countable_of_injOn
    (f := fun A : Set ℕ => ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))
    (t := Set.range ((↑) : ℚ → ℝ)) ?_ ?_ (Set.countable_range _)
  · rintro A ⟨_, q, hq⟩
    exact ⟨q, hq.symm⟩
  · rintro A ⟨hA, _⟩ B ⟨hB, _⟩ h
    exact Opn.erdos_257_subsum_injective A B hA hB h
