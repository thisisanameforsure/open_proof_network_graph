/-
Copyright 2025 The Formal Conjectures Authors.

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
import Defs.CombinatoricsSimpleGraphEdgeColouring
import Defs.CombinatoricsSimpleGraphHypercube
import Defs.CombinatoricsSimpleGraphRamsey
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/567.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 567

Let $G$ be either $Q_3$ or $K_{3,3}$ or $H_5$ (the last formed by adding two vertex-disjoint chords
to $C_5$). Is it true that, if $H$ has $m$ edges and no isolated vertices, then
$$ R(G,H) \ll m? $$

In other words, is $G$ Ramsey size linear? A special case of Problem 566.

*Reference:* [erdosproblems.com/567](https://www.erdosproblems.com/567)

[EFRS93] Erdős, Faudree, Rousseau and Schelp, _Ramsey size linear graphs_.
Combin. Probab. Comput. (1993), 389-399.
-/

section

namespace Erdos567

open SimpleGraph
open scoped Finset

/-- $Q_3$ is the 3-dimensional hypercube graph (8 vertices, 12 edges).
Vertices are 3-bit vectors. Two vertices are adjacent iff they differ in exactly one bit. -/
abbrev Q3 : SimpleGraph (Fin 3 → Bool) := hypercube 3

/-- $K_{3,3}$ is the complete bipartite graph with partition sizes 3, 3 (6 vertices, 9 edges). -/
def K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

/-- $H_5$ is $C_5$ with two vertex-disjoint chords (5 vertices, 7 edges).
Also known as $K_4^*$ (the graph obtained from $K_4$ by subdividing one edge). -/
def H5 : SimpleGraph (Fin 5) :=
  .cycleGraph 5 ⊔ .edge 0 2 ⊔ .edge 1 3

end Erdos567
