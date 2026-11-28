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
import Defs.AlgebraOrderGroupPointwiseInterval
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsAPBasic
import Defs.CombinatoricsAdditiveVCDim
import Defs.CombinatoricsSetFamilyVCDim
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataSetDensity
import Defs.DataSetInterval
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.OrderIntervalFinsetBasic
import Defs.OrderIntervalFinsetNat

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/39.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Green's Open Problem 39

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.39)
- [BJR11] Bollobás, Béla, Svante Janson, and Oliver Riordan. "On covering by translates of a set."
  Random Structures & Algorithms 38.1‐2 (2011): 33-67.
-/

section

open Filter Topology
open scoped Pointwise

namespace Green39

/--
The proportion of subsets of $\mathbb{Z}/p\mathbb{Z}$ of size $k$ that can cover
$\mathbb{Z}/p\mathbb{Z}$ using at most $c$ translates.

If p = 0 or k > p, return 0 by convention.
-/
def proportionCoverable (p k c : ℕ) : ℚ :=
  if h : p = 0 then 0
  else if k > p then 0
  else
    have : NeZero p := ⟨h⟩
    let S : Finset (Finset (ZMod p)) := Finset.powersetCard k Finset.univ
    let coverable := S.filter (fun A => ∃ T : Finset (ZMod p), T.card ≤ c ∧ A + T = Finset.univ)
    (coverable.card : ℚ) / (S.card : ℚ)

end Green39
