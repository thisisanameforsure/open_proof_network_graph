import Mathlib
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsSimpleGraphCircumference
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataNatPrimeFinset
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local
import Nodes.«erdos-883--h1».Context
open Filter
open scoped Classical
open Erdos883

/-! Non-vacuity witness: n = 12, A = {1, …, 12} (12 elements, more than 12/2 + 12/3 − 12/6 = 8), and the odd length l = 5 ≤ 12/3 + 1 = 5. -/

theorem witness : ∃ (n : ℕ) (A : Finset ℕ) (l : ℕ),
  A ⊆ Finset.Icc (1 : ℕ) n ∧
    n / (2 : ℕ) + n / (3 : ℕ) - n / (6 : ℕ) < A.card ∧ Odd l ∧ (5 : ℕ) ≤ l ∧ l ≤ n / (3 : ℕ) + (1 : ℕ) :=
  ⟨12, Finset.Icc 1 12, 5, Finset.Subset.refl _, by simp, ⟨2, rfl⟩, by norm_num, by norm_num⟩
