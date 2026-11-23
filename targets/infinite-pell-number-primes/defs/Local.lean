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

/-! Ported mechanically from `FormalConjectures/Wikipedia/Pell.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Infinitude of Pell number primes

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Pell_number#Primes_and_squares)
 - [A86383](https://oeis.org/A86383)

The Pell numbers $P_n$ are defined by $P_0 = 0$,
$P_1 = 1$, $P_{n+2} = 2*P_{n+1} + P_n$. [OEIS A129](https://oeis.org/A129)

The conjecture says that there are infinitely many prime Pell numbers.
-/

section

namespace PellNumbers

/-- The *Pell numbers* $P_n$ are defined by $P_0 = 0$, $P_1 = 1$, $P_{n+2} = 2*P_{n+1} + P_n$ -/
def pellNumber : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 + 1 => 2 * pellNumber (n + 1) + pellNumber n

-- TODO : Formalise connection between Pell numbers and Pell equation x^2 - 2*y^2 = -1

end PellNumbers
