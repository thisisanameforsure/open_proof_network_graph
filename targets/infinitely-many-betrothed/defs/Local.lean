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

/-! Ported mechanically from `FormalConjectures/Wikipedia/BetrothedNumbers.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Betrothed numbers

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Betrothed_numbers)
- [OEIS A005276](https://oeis.org/A005276)
-/

section

namespace BetrothedNumbers

open scoped ArithmeticFunction.sigma

/--
Two natural numbers $m$ and $n$ are **betrothed**  (or quasi-amicable) if $\sigma(m) = \sigma(n) = m + n + 1$,
where $\sigma$ is the sum-of-divisors function. Equivalently, the sum of the proper divisors
of $m$ equals $n + 1$, and the sum of the proper divisors of $n$ equals $m + 1$.
-/
@[mk_iff]
structure IsBetrothed (m n : ℕ) : Prop where
  left : σ 1 m = m + n + 1
  right : σ 1 n = m + n + 1

end BetrothedNumbers
