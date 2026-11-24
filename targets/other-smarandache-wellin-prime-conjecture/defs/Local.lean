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
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.CombinatoricsSimpleGraphCycle
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Other/SmarandacheWellinPrime.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Smarandache–Wellin primes

The Smarandache–Wellin numbers are formed by concatenating the decimal expansions of the
successive primes: $2, 23, 235, 2357, \ldots$. It is conjectured that infinitely many members of
this sequence are prime.

*References:*
* [Smarandache Problems](https://fs.unm.edu/S-PROBL.HTM)
* [OEIS A019518](https://oeis.org/A019518)
* [OEIS A069151](https://oeis.org/A069151)
* [OEIS A046035](https://oeis.org/A046035)
-/

section

namespace SmarandacheWellinPrime

/-- The number of decimal digits of a natural number, counting zero as one digit. -/
def decimalDigitCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else (Nat.digits 10 n).length

/-- Append the decimal expansion of `right` to that of `left`. -/
def decimalAppend (left right : ℕ) : ℕ :=
  left * 10 ^ decimalDigitCount right + right

/-- The Smarandache–Wellin sequence, indexed from zero. -/
noncomputable def a : ℕ → ℕ
  | 0 => 2
  | n + 1 => decimalAppend (a n) ((n + 1).nth Nat.Prime)

end SmarandacheWellinPrime
