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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/685.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 685

*References:*
- [erdosproblems.com/685](https://www.erdosproblems.com/685)
- [Er79d] Erdős, P., *Some unconventional problems in number theory*. Acta Math. Acad. Sci.
  Hungar. (1979), 71-80.
-/

section

open Filter
open scoped ArithmeticFunction.omega

namespace Erdos685

/-- `primeRecipSum k n` is the sum of $1/p$ over the primes $k < p < n$. -/
noncomputable def primeRecipSum (k n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioo k n).filter Nat.Prime, (1 : ℝ) / p

end Erdos685
