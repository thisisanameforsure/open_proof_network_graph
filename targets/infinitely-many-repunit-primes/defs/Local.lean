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

/-! Ported mechanically from `FormalConjectures/Wikipedia/RepunitPrime.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Decimal Repunit Primes

A decimal repunit is a natural number whose decimal representation consists entirely of ones.
It is conjectured that infinitely many decimal repunits are prime.

*References:*
- [Wikipedia: Repunit](https://en.wikipedia.org/wiki/Repunit#Decimal_repunit_primes)
- [OEIS A002275](https://oeis.org/A002275)
- [OEIS A004022](https://oeis.org/A004022)
- [OEIS A004023](https://oeis.org/A004023)
-/

section

namespace RepunitPrime

/-- The decimal repunit of length $n$, defined as $1 + 10 + \cdots + 10^{n-1}$. -/
def repunit10 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 10 ^ i

end RepunitPrime
