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
import Defs.AnalysisSpecialFunctionsAdditiveCharacter

/-! Ported mechanically from `FormalConjectures/Wikipedia/WilsonPrime.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Wilson primes

A Wilson prime is a prime $p$ for which $p^2$ divides $(p-1)!+1$. The only known examples are
$5$, $13$, and $563$. It is conjectured that infinitely many Wilson primes exist.

*References:*
* [Wikipedia, Wilson prime](https://en.wikipedia.org/wiki/Wilson_prime)
* [OEIS A007540](https://oeis.org/A007540)
* E. Costa, R. Gerbicz, and D. Harvey,
  [A search for Wilson primes](https://arxiv.org/abs/1209.3436)
-/

section

namespace WilsonPrime

/-- A Wilson prime is a prime $p$ such that $p^2 \mid (p-1)!+1$. -/
def IsWilsonPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ (p - 1).factorial + 1

end WilsonPrime
