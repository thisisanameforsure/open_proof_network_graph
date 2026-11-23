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
import Defs.CombinatoricsSimpleGraphEdgeColouring
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/1111.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 1111

*References:*
- [erdosproblems.com/1111](https://www.erdosproblems.com/1111)
- [ElEr85] El-Zahar, M. and Erdős, P., *On the existence of two non-neighboring subgraphs in a
  graph*. Combinatorica 5 (1985), 295-300.
- [NSS24] Nguyen, T., Scott, A. and Seymour, P., *On a problem of El-Zahar and Erdős*.
  J. Combin. Theory Ser. B 165 (2024), 211-222. [arXiv:2303.13449](https://arxiv.org/abs/2303.13449)
- [Wa80b] Wagon, S., *A bound on the chromatic number of graphs without certain induced
  subgraphs*. J. Combin. Theory Ser. B 29 (1980), 345-346.
-/

section

namespace Erdos1111

/-- Two sets `A` and `B` of vertices of `G` are *anticomplete* if they are disjoint and `G` has
no edge between `A` and `B`. -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

end Erdos1111
