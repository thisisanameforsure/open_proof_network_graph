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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/573.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 573

*References:*
- [erdosproblems.com/573](https://www.erdosproblems.com/573)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer.
  (1975), 3-14.
- [ErSi82] Erdős, P. and Simonovits, M., *Compactness results in extremal graph theory*.
  Combinatorica (1982), 275-288.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [KST54] Kővári, T. and Sós, V. T. and Turán, P., *On a problem of K. Zarankiewicz*.
  Colloq. Math. (1954), 50-57.
-/

section

open Filter Asymptotics SimpleGraph

namespace Erdos573

open scoped Classical in
/-- $\mathrm{ex}(n;\{C_k : k \in L\})$: the greatest number of edges of a simple graph on `n`
vertices that contains no cycle $C_k$ with $k \in L$ as a (not necessarily induced) subgraph.

`cycleGraph k` is the cycle on `Fin k`. The definition is meaningful only for sets `L` of
lengths `k ≥ 3`, which are the only ones used below: `cycleGraph 0` and `cycleGraph 1` have no
edges, and `cycleGraph 2` is a single edge. -/
noncomputable def cycleExtremalNumber (L : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) => ∀ k ∈ L, (cycleGraph k).Free G).sup
    fun G => G.edgeFinset.card

end Erdos573
