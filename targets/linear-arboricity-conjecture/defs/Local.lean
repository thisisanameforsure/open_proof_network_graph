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
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Wikipedia/LinearArboricityConjecture.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The linear arboricity conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Linear_arboricity)
* [AEH81] Akiyama, J., Exoo, G., and Harary, F. (1981). "Covering and packing in graphs. IV.
  Linear arboricity." *Networks* 11, pp. 69--72.
* [EP84] Enomoto, H. and Péroche, B. (1984). "The linear arboricity of some regular graphs."
  *J. Graph Theory* 8, pp. 309--324.
* [Al88] Alon, N. (1988). "The linear arboricity of graphs." *Israel J. Math.* 62,
  pp. 311--325.
-/

section

namespace LinearArboricityConjecture

variable {V : Type*}

/-- A **linear forest** is a graph whose connected components are paths: an acyclic graph in
which every vertex has at most two neighbours. -/
def IsLinearForest (F : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ ∀ v, (F.neighborSet v).ncard ≤ 2

/-- `G` decomposes into `k` linear forests: there are `k` linear-forest subgraphs of `G`
such that every edge of `G` lies in exactly one of them. -/
def HasLinearForestDecomposition (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : Fin k → SimpleGraph V, (∀ i, IsLinearForest (D i) ∧ D i ≤ G) ∧
    ∀ u v, G.Adj u v ↔ ∃! i, (D i).Adj u v

/-- The **linear arboricity** `la(G)`: the least number of linear forests into which the edges
of `G` can be partitioned. -/
noncomputable def linearArboricity (G : SimpleGraph V) : ℕ :=
  sInf {k | HasLinearForestDecomposition G k}

end LinearArboricityConjecture
