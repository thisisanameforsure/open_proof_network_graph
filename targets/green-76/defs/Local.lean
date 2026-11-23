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

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/76.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Ben Green's Open Problem 76

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.76)
- [AES10] Aronov, Boris, Esther Ezra, and Micha Sharir. "Small-size $\varepsilon$-nets for
  axis-parallel rectangles and boxes." SIAM Journal on Computing 39.7 (2010): 3248-3282.
  [doi:10.1137/090762968](https://doi.org/10.1137/090762968)
- [PT11] Pach, János. "Boxes and the art of $\varepsilon$-net maintenance." Invited problems,
  2nd Emléktábla Workshop (2011), Problem 5 (Pach and Tardos).
  [PDF](https://www.renyi.hu/~emlektab/emlektabla2withresults.pdf)
- [PT13] Pach, János, and Gábor Tardos. "Tight lower bounds for the size of epsilon-nets."
  Journal of the American Mathematical Society 26.3 (2013): 645-658.
  [doi:10.1090/S0894-0347-2012-00759-0](https://doi.org/10.1090/S0894-0347-2012-00759-0),
  [arXiv:1012.1240](https://arxiv.org/abs/1012.1240)
-/

section

open scoped Finset

namespace Green76

/--
`HitsRichRectangles k A A'` says that every closed axis-parallel rectangle that contains at least
$k$ points of $A$ also contains a point of $A'$.

For $a = (a_1, a_2)$ and $b = (b_1, b_2)$, `Set.Icc a b` is the rectangle
$[a_1, b_1] \times [a_2, b_2]$. It is empty if $a_1 > b_1$ or $a_2 > b_2$, and it can be a segment
or a point.
-/
def HitsRichRectangles (k : ℕ) (A A' : Finset (ℝ × ℝ)) : Prop :=
  ∀ a b : ℝ × ℝ, k ≤ #{p ∈ A | p ∈ Set.Icc a b} → ∃ p ∈ A', p ∈ Set.Icc a b

end Green76
