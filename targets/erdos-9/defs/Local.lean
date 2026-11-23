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
import Defs.AlgebraOrderGroupPointwiseInterval
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.DataSetDensity
import Defs.DataSetInterval
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.OrderIntervalFinsetBasic
import Defs.OrderIntervalFinsetNat

/-! Ported mechanically from `FormalConjectures/ErdosProblems/9.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 9

*Reference:* [erdosproblems.com/9](https://www.erdosproblems.com/9)
-/

section

namespace Erdos9

/--
The set of odd numbers that cannot be expressed as a prime plus two powers of 2.
-/
def Erdos9A : Set ℕ := { n | Odd n ∧ ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l }

end Erdos9
