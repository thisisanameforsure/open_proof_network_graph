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

/-! Ported mechanically from `FormalConjectures/Wikipedia/PollocksConjecture.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Pollock's (tetrahedral numbers) conjecture

Every positive integer is the sum of at most 5 tetrahedral numbers.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Pollock%27s_conjectures)
- [A797](https://oeis.org/A797)
- L. E. Dickson, *History of the Theory of Numbers, Vol. II: Diophantine Analysis*, Dover (2005), pp. 22–23
- Frederick Pollock, *On the extension of the principle of Fermat's theorem on the polygonal numbers to the higher order of series whose ultimate differences are constant*, Abstracts of the Papers Communicated to the Royal Society of London **5** (1850), 922–924
- H. E. Salzer and N. Levine, *Table of integers not exceeding 100000 that are not expressible as the sum of four tetrahedral numbers*, Math. Comp. **12** (1958), 141–144
- [MathWorld: Pollock's Conjecture](https://mathworld.wolfram.com/PollocksConjecture.html)
-/

section

namespace PollocksConjecture

open scoped BigOperators

/-  ## Definitions -/

/-- The $n$-th tetrahedral number: $T_n = \frac{n(n+1)(n+2)}{6}$. -/
def tetrahedral (n : ℕ) : ℕ :=
  n * (n + 1) * (n + 2) / 6

/-  ## Auxiliary definition -/

/-- The set of natural numbers that are **not** a sum of $4$ tetrahedral numbers. -/
def NotSumOfFourTetrahedral : Set ℕ :=
  {N : ℕ | ∀ f : Fin 4 → ℕ, N ≠ ∑ i, tetrahedral (f i)}

/-  ## Statements -/

end PollocksConjecture
