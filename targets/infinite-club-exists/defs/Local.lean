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

/-! Ported mechanically from `FormalConjectures/Wikipedia/SolitaryNumber.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Solitary Numbers

*References:*
- [Solitary number (Wikipedia)](https://en.wikipedia.org/wiki/Solitary_number)
- [Solitary number large clubs (Wikipedia)](https://en.wikipedia.org/wiki/Solitary_number#Large_clubs)
-/

section

open ArithmeticFunction.sigma

namespace SolitaryNumber

/--
Two positive integers $m$ and $n$ are friendly if they have the same abundancy index, that
is $\sigma(m) / m = \sigma(n) / n$, expressed via cross-multiplication to avoid rationals.
-/
def Friendly (m n : ℕ) : Prop := 0 < m ∧ 0 < n ∧ σ 1 m * n = σ 1 n * m

/--
A positive integer $n$ is solitary if every friend of $n$ is equal to $n$, i.e. its
abundancy class is the singleton $\{n\}$.
-/
def IsSolitary (n : ℕ) : Prop := 0 < n ∧ ∀ m, Friendly m n → m = n

end SolitaryNumber
