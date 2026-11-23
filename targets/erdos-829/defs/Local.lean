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
import Defs.AlgebraGroupIndicator
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsAdditiveConvolution
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/829.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 829

*References:*
- [erdosproblems.com/829](https://www.erdosproblems.com/829)
- [Er83] Erdős, P. and Dudley, U., _Some remarks and problems in number theory related to the
  work of Euler_. Math. Mag. (1983), 292-298.
-/

section

open AdditiveCombinatorics Asymptotics Filter

namespace Erdos829

/-- The set of perfect cubes in $\mathbb{N}$. -/
def cubes : Set ℕ := {n | ∃ k, k ^ 3 = n}

namespace variants

end variants

end Erdos829
