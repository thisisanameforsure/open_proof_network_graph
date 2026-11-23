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
import Defs.CombinatoricsSimpleGraphEdgeColouring
import Defs.CombinatoricsSimpleGraphRamsey
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/545.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 545

*References:*
- [erdosproblems.com/545](https://www.erdosproblems.com/545)
- [ErGr75] Erdős, P. and Graham, R. L., On partition theorems for finite graphs.
  Infinite and finite sets (1975), 515-527.
- [Er84b] Erdős, P., On some problems in graph theory, combinatorial analysis and combinatorial
  number theory. Graph theory and combinatorics (Cambridge, 1983) (1984), 1-17.
-/

section

open Filter

namespace Erdos545

/--
The graph formed by connecting a new vertex (`none`) to $t$ of the vertices of $K_n$ (`Fin n`).
-/
def knPlusTEdges (n t : ℕ) : SimpleGraph (Option (Fin n)) where
  Adj u v := match u, v with
    | some x, some y => x ≠ y
    | none, some y => y.val < t
    | some x, none => x.val < t
    | none, none => False
  symm.symm u v := by
    cases u <;> cases v <;> simp [ne_comm]
  loopless.irrefl u := by
    cases u <;> simp

-- TODO: Add variants of the problem.

end Erdos545
