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

/-! Ported mechanically from `FormalConjectures/Wikipedia/LychrelNumbers.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Lychrel numbers in base 10

A (base-10) *Lychrel number* is a positive integer which never becomes a palindrome under the
iteration

$$a_{0} = n, \qquad a_{k+1} = a_k + \operatorname{rev}_{10}(a_k).$$

One commonly stated conjectural direction is that there are no Lychrel numbers in base 10.
The smallest widely studied open case is `196`.

*References:*
* [Wikipedia: Lychrel number](https://en.wikipedia.org/wiki/Lychrel_number)
* [MathWorld: Lychrel Number](https://mathworld.wolfram.com/LychrelNumber.html)
* [OEIS A023108](https://oeis.org/A023108)
* [OEIS A023109](https://oeis.org/A023109)
-/

section

namespace LychrelNumbers

/-- The base (10) used for digit reversal. -/
abbrev base : ℕ := 10

/--
The digit-reversal map $\operatorname{rev}_{10}(n)$.

Implementation note: `Nat.digits base n` returns the digits of `n` in *little-endian* order.
Reversing this list and interpreting it again as little-endian digits gives the usual digit
reversal.
-/
def rev10 (n : ℕ) : ℕ :=
  Nat.ofDigits base (Nat.digits base n).reverse

/-- A number is a (base-10) palindrome if it equals its digit reversal. -/
def IsPalindrome10 (n : ℕ) : Prop :=
  rev10 n = n

/-- One step of the Lychrel iteration: `n ↦ n + rev10 n`. -/
def lychrelStep (n : ℕ) : ℕ :=
  n + rev10 n

/-- The number $n$ is a (base-10) Lychrel number if no iterate of the Lychrel process is a palindrome. -/
def IsLychrel10 (n : ℕ) : Prop :=
  ∀ k : ℕ, ¬ IsPalindrome10 (lychrelStep^[k] n)

end LychrelNumbers
