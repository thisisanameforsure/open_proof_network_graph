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
import Defs.DataSymSym2
import Defs.FieldTheoryMilnorKTheory
import Defs.GeometryEuclidean
import Defs.GeometryMetric
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/1088.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 1088

*Reference:* [erdosproblems.com/1088](https://www.erdosproblems.com/1088)
-/

section

open Filter
open scoped EuclideanGeometry

namespace Erdos1088

variable {d : ℕ}

/-- A finite set of points has all pairwise distances distinct. -/
def PairwiseDistancesDistinct (A : Finset (ℝ^d)) : Prop :=
  distinctDistances A = Nat.choose A.card 2

/-- The finite set `S` contains an `n`-point subset with all pairwise distances distinct. -/
def HasSubsetWithDistinctDistances (n : ℕ) (S : Finset (ℝ^d)) : Prop :=
  ∃ A : Finset (ℝ^d), A ⊆ S ∧ A.card = n ∧ PairwiseDistancesDistinct A

/--
The set of cardinalities `m` such that every `m`-point subset of `ℝ^d` contains an `n`-point
subset with all pairwise distances distinct.
-/
def cardSet (d n : ℕ) : Set ℕ :=
  { m | n ≤ m ∧ ∀ S : Finset (ℝ^d), S.card = m → HasSubsetWithDistinctDistances n S }

/--
The least `m` such that every `m`-point subset of `ℝ^d` contains an `n`-point subset with all
pairwise distances distinct.
-/
noncomputable def f (d n : ℕ) : ℕ := sInf (cardSet d n)

end Erdos1088
