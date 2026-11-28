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
import Defs.CombinatoricsHypergraphBasic
import Defs.CombinatoricsHypergraphFinite
import Defs.CombinatoricsHypergraphUniform
import Defs.CombinatoricsSetFamilyPropertyB
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.CombinatoricsSimpleGraphCycle
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/740.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 740: Infinitary version of chromatic number and odd cycles

*Reference:* [erdosproblems.com/740](https://erdosproblems.com/740)
-/

section

open scoped Cardinal

namespace Erdos740

/-- A graph avoids odd cycles of length $\leq r$ if it contains no odd cycles of length at most $r$. -/
def NoShortOddCycle {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → Odd c.length → c.length > r

-- TODO: add the related infinitary chromatic-number statements from erdosproblems.com.

end Erdos740
