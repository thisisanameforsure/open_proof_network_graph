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
import Defs.DataNatMaxPrimeFac
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/368.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 368

*References:*
- [erdosproblems.com/368](https://www.erdosproblems.com/368)
- [Er76d] Erdős, P., Problems and results on number theoretic properties of consecutive
  integers and related questions. Proceedings of the Fifth Manitoba Conference on Numerical
  Mathematics (1976), 25–44.
- [Po18] Pólya, Georg, Zur arithmetischen Untersuchung der Polynome.
  Math. Z. (1918), 143–148.
- [Sc67b] Schinzel, A., On two theorems of Gelfond and some of their applications.
  Acta Arith. (1967/68), 177–236.
-/

section

namespace Erdos368

open Filter

/-- The largest prime factor of $n(n+1)$. -/
def F (n : ℕ) : ℕ := (n * (n + 1)).maxPrimeFac

end Erdos368
