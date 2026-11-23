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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Wikipedia/ElliottHalberstamConjecture.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Elliott–Halberstam conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Elliott%E2%80%93Halberstam_conjecture)
- [EH68] Elliott, Peter D. T. A. and Halberstam, Heini, *A conjecture in prime number
  theory*, Symposia Mathematica, Vol. IV (INDAM, Rome, 1968/69), 59–72.
- [FG89] Friedlander, John and Granville, Andrew, *Limitations to the equi-distribution of
  primes I*, Ann. of Math. (2) 129 (1989), no. 2, 363–382.
-/

section

namespace ElliottHalberstamConjecture

/--
$\pi(x; q, a)$: the number of primes $p \le x$ with $p \equiv a \pmod q$.
-/
def primesInAPCount (x q : ℕ) (a : ZMod q) : ℕ :=
  ((Finset.range (x + 1)).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a).card

/--
The error term
$$E(x; q) = \max_{\gcd(a,q)=1} \left|\pi(x;q,a) - \frac{\pi(x)}{\varphi(q)}\right|,$$
measuring the deviation of the primes in the arithmetic progressions modulo $q$ from
uniform distribution among the $\varphi(q)$ coprime residue classes.
-/
noncomputable def E (x q : ℕ) : ℝ :=
  ⨆ a : (ZMod q)ˣ, |(primesInAPCount x q a : ℝ) - (x.primeCounting : ℝ) / (q.totient : ℝ)|

end ElliottHalberstamConjecture
