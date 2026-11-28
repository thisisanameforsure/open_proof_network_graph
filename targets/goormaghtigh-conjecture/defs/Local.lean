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

/-! Ported mechanically from `FormalConjectures/Wikipedia/Goormaghtigh.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The Goormaghtigh conjecture

A repunit is a number whose digits in some base are all $1$. Here a nontrivial representation has
at least three digits. The Goormaghtigh conjecture says that $31$ and $8191$ are the only numbers
having nontrivial repunit representations in two different bases.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Goormaghtigh_conjecture)
* J. Grantham,
  [No new Goormaghtigh primes up to $10^{700}$](https://math.colgate.edu/~integers/y98/y98.pdf)
-/

section

namespace Goormaghtigh

/-- The repunit with `digits` digits in the given base, expressed without division. -/
def repunit (base digits : ℕ) : ℕ :=
  ∑ i ∈ Finset.range digits, base ^ i

/-- A number having repunit representations of at least three digits in two distinct bases. -/
def IsGoormaghtighNumber (N : ℕ) : Prop :=
  ∃ base₁ base₂ digits₁ digits₂ : ℕ,
    2 ≤ base₁ ∧ 2 ≤ base₂ ∧ base₁ ≠ base₂ ∧
      3 ≤ digits₁ ∧ 3 ≤ digits₂ ∧
        repunit base₁ digits₁ = N ∧ repunit base₂ digits₂ = N

end Goormaghtigh
