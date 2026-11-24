/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsAPBasic
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataSetTriplewise
import Defs.DataSymSym2
import Defs.FieldTheoryMilnorKTheory
import Defs.Geometry2d
import Defs.GeometryMetric
import Defs.GroupTheoryRationalClasses
import Defs.LogicEquivFinRotate
import Defs.TopologyMetricSpaceMetricSeparated

/-! Ported mechanically from `FormalConjectures/ErdosProblems/103.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 103

*References:*
- [erdosproblems.com/103](https://www.erdosproblems.com/103)
-/

section

open Filter EuclideanGeometry

namespace Erdos103

/-- The sets of $n$ points in $\mathbb{R}^2$ whose pairwise distances are all at least $1$. -/
def separatedSets (n : ℕ) : Set (Finset ℝ²) :=
  {B | B.card = n ∧ Metric.IsSeparated' 1 (B : Set ℝ²)}

/-- `A` is a *minimiser* for `n` if it is a separated set of `n` points whose diameter is at
most the diameter of every separated set of `n` points (compare `Erdos99.erdos_99`). -/
def IsMinimiser (n : ℕ) (A : Finset ℝ²) : Prop :=
  A ∈ separatedSets n ∧
    IsMinOn (fun B : Finset ℝ² => Metric.diam (B : Set ℝ²)) (separatedSets n) A

/-- Two finite sets of points are *congruent* if an isometry of the plane maps one onto the
other. -/
def Congruent (A B : Finset ℝ²) : Prop :=
  ∃ f : ℝ² ≃ᵢ ℝ², f '' A = B

/-- `h n` is the number of congruence classes of minimisers for `n` points, as an element of
`ℕ∞`: the supremum of the cardinalities of finite families of pairwise incongruent minimisers,
which is `⊤` when there are infinitely many classes. -/
noncomputable def h (n : ℕ) : ℕ∞ :=
  ⨆ (S : Finset (Finset ℝ²)) (_ : (∀ A ∈ S, IsMinimiser n A) ∧
      ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Congruent A B), (S.card : ℕ∞)

end Erdos103
