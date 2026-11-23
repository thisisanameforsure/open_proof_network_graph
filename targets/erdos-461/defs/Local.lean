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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/461.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 461

*References:*
- [erdosproblems.com/461](https://www.erdosproblems.com/461)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
-/

section

namespace Erdos461

/-- The $t$-smooth component $s_t(n)$ of $n$: the product of all primes $p < t$ dividing $n$,
counted with multiplicity. -/
def smoothComponent (t n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· < t)).prod

/-- The number $f(n,t)$ of distinct values of $s_t(m)$ for $m \in [n+1, n+t]$. -/
def f (n t : ℕ) : ℕ :=
  ((Finset.Icc (n + 1) (n + t)).image (smoothComponent t)).card

end Erdos461
