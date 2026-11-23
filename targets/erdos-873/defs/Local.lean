/-
Copyright 2025 The Formal Conjectures Authors.

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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/873.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 873

*References:*
- [erdosproblems.com/873](https://www.erdosproblems.com/873)
- [Er92c] Erdős, P., Some of my forgotten problems in number theory. Hardy-Ramanujan J. 15
  (1992), 34-50.
-/

section

namespace Erdos873

/-- Let $a$ be some sequence of natural numbers. We set $F(A,X,k)$ to be the count of
the number of $i$ such that $[a_i,a_{i+1}, \dots ,a_{i+k−1}] < X$,
where the left-hand side is the least common multiple. -/
noncomputable abbrev F (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (Finset.range k).lcm (fun m => a (i + m)) < X}.encard

/-
## Statements following the original question

The paper states (2), (3), and then conjectures an all-X strengthening of (3).
-/

end Erdos873
