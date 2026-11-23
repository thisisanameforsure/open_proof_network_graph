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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/642.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 642

*References:*
- [erdosproblems.com/642](https://www.erdosproblems.com/642)
- [CES96] Chen, Guantao and Erdős, Paul and Staton, William, *Proof of a conjecture of Bollobás
  on nested cycles*. J. Combin. Theory Ser. B (1996), 38--43.
- [DMMS24] Draganić, Nemanja and Methuku, Abhishek and Munhá Correia, David and Sudakov,
  Benny, *Cycles with many chords*. Random Structures Algorithms (2024), 3--16.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math.
  (1997), 81-85.
-/

section

open Filter

namespace Erdos642

/-- Every cycle of the graph `G` has more vertices than chords.

A cycle is a closed walk `c` with `c.IsCycle`. It has `c.length` vertices. A chord of `c` is an
edge of `G` between two vertices of `c` that is not an edge of `c`
(`SimpleGraph.Walk.IsChord`). -/
def CyclesHaveMoreVerticesThanChords {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → {e : Sym2 V | c.IsChord e}.ncard < c.length

open scoped Classical in
/-- The maximal number $f(n)$ of edges of a graph on `n` vertices in which every cycle has more
vertices than chords. There are finitely many graphs on `Fin n`, so the supremum is a maximum. -/
noncomputable def maxEdges (n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) => CyclesHaveMoreVerticesThanChords G).sup
    fun G => G.edgeSet.ncard

end Erdos642
