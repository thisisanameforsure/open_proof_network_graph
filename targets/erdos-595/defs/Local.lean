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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/595.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 595

*References:*
- [erdosproblems.com/595](https://www.erdosproblems.com/595)
- [Er87] Erdős, Paul, Problems and results on set systems and hypergraphs. Extremal problems
  for finite sets (Visegrád, 1991), Bolyai Soc. Math. Stud. (1994), 217-227.
- [Fo70] Folkman, Jon, Graphs with monochromatic complete subgraphs in every edge coloring.
  SIAM J. Appl. Math. (1970), 19:340-345.
- [NeRo75] Nešetřil, Jaroslav and Rödl, Vojtěch, Type theory of partition problems of graphs.
  Recent advances in graph theory (Proc. Second Czechoslovak Sympos., Prague, 1974),
  Academia, Prague (1975), 405-412.
-/

section

open SimpleGraph Set

namespace Erdos595

def IsCountableUnionOfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-
## Main open problem
-/

/-
## Variants and partial results
-/

end Erdos595
