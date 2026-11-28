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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/864.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 864

*References:*
- [erdosproblems.com/864](https://www.erdosproblems.com/864)
- [A389182](https://oeis.org/A389182)
- [ErFr91] Erdős, P. and Freud, R., *On sums of a Sidon-sequence*. J. Number Theory 38 (1991),
  196--205.
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy-Ramanujan J. 15
  (1992), 34-50.
-/

section

open Filter
open scoped Finset

namespace Erdos864

/-- The representations of $n$ as a sum $n = a + b$ with $a \leq b$ and $a, b \in A$, recorded as
the pairs $(a, b)$. The case $a = b$ is allowed. -/
def sumRepresentations (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ A ×ˢ A | p.1 ≤ p.2 ∧ p.1 + p.2 = n}

/-- There is at most one $n$ with more than one representation $n = a + b$, where $a \leq b$ and
$a, b \in A$. That is, any two integers with more than one representation are equal.

Every Sidon set satisfies this condition, since then no $n$ has more than one representation. -/
def HasAtMostOneRepeatedSum (A : Finset ℕ) : Prop :=
  ∀ n m : ℕ, 1 < #(sumRepresentations A n) → 1 < #(sumRepresentations A m) → n = m

end Erdos864
