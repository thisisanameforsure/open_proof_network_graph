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
import Defs.AlgebraOrderGroupPointwiseInterval
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.DataSetDensity
import Defs.DataSetInterval
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.OrderIntervalFinsetBasic
import Defs.OrderIntervalFinsetNat

/-! Ported mechanically from `FormalConjectures/ErdosProblems/770.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 770

*References:*
 - [erdosproblems.com/770](https://www.erdosproblems.com/770)
 - [Er49d] Erdös, P. "On the strong law of large numbers." Transactions of the American Mathematical
    Society 67.1 (1949): 51-56.
 - [Ma66] Matsuyama, Noboru. "On the strong law of large numbers." Tohoku Mathematical Journal,
    Second Series 18.3 (1966): 259-269.
-/

section

open Set ENat Filter

namespace Erdos770

/-- Let $h n$ be the minimal number such that $2 ^ n - 1, \dots, h(n) ^ n - 1$
are collectively coprime. -/
noncomputable def h (n : ℕ) : ℕ∞ := sInf {m | 2 < m ∧
  ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}

end Erdos770
