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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Paper/Dubner.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Dubner's conjecture

*Reference*: [Every even number greater than 4208 is the sum of two t-primes](https://scispace.com/pdf/twin-prime-conjectures-3icaxy6b0m.pdf)
by *Harvey Dubner*.
-/

section

namespace DubnerConjecture

/--
A twin prime is a prime number that has a prime gap of 2, meaning either p - 2 or p + 2
is also prime.
-/
def IsTwinPrime (p : ℕ) : Prop :=
  p.Prime ∧ ((p - 2).Prime ∨ (p + 2).Prime)

end DubnerConjecture
