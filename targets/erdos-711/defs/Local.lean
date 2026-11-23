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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/711.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 711

*References:*
- [erdosproblems.com/711](https://www.erdosproblems.com/711)
- [ErPo80] Erdős, P. and Pomerance, C.,
  *Matching the natural numbers up to $n$ with distinct multiples in another interval* (1980).
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*.
  Hardy-Ramanujan J. (1992), 34–50.
- [vD26] van Doorn, W.,
  [*On the length of an interval that contains distinct multiples of the first $n$ positive
  integers*](https://arxiv.org/abs/2601.16972). Integers 26 (2026), #A7.
-/

section

namespace Erdos711

open Filter Asymptotics

/-- There are distinct $a_1,\ldots,a_n$ in the open interval $(m,m+L)$ such that
$i \mid a_i$ for every $1 \leq i \leq n$. -/
def HasDivisibleDistinctTuple (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ,
    Function.Injective a ∧
      ∀ i : Fin n, m < a i ∧ a i < m + L ∧ (i.val + 1) ∣ a i

/-- $L$ is the minimal interval length for the parameters $(n,m)$. -/
def IsMinimalIntervalLength (n m L : ℕ) : Prop :=
  HasDivisibleDistinctTuple n m L ∧
    ∀ L', HasDivisibleDistinctTuple n m L' → L ≤ L'

-- TODO: Formalize the Erdős–Pomerance bounds and van Doorn's stronger quantitative theorem.

end Erdos711
