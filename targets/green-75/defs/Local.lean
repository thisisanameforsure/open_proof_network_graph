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

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/75.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Ben Green's Open Problem 75

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.75)
- [CL25] Conlon, D. and Lim, J., *Everywhere unbalanced configurations*. Adv. Math. 480 (2025),
  Paper No. 110445. [arXiv:2308.02466](https://arxiv.org/abs/2308.02466)
- [Pi03] Pinchasi, R., *Lines with many points on both sides*. Discrete Comput. Geom. 30 (2003),
  415-435. [doi:10.1007/s00454-003-2826-8](https://doi.org/10.1007/s00454-003-2826-8)
-/

section

open scoped Finset

namespace Green75

/--
`cross p q x` is the cross product $(q - p) \times (x - p)$. For $p \neq q$ it is positive if `x`
lies strictly to the left of the line from `p` to `q`, negative if `x` lies strictly to the right,
and zero if `x` lies on the line `pq`.
-/
def cross (p q x : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (x.2 - p.2) - (q.2 - p.2) * (x.1 - p.1)

/-- The number of points of `X` strictly to the left of the line from `p` to `q`. -/
noncomputable def leftCount (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℕ :=
  #{x ∈ X | 0 < cross p q x}

/-- The number of points of `X` strictly to the right of the line from `p` to `q`. -/
noncomputable def rightCount (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℕ :=
  #{x ∈ X | cross p q x < 0}

/--
`imbalance X p q` is the absolute difference between the numbers of points of `X` on the two sides
of the line through
`p` and `q`. The points of `X` on the line itself are on neither side.
-/
noncomputable def imbalance (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℤ :=
  |(leftCount X p q : ℤ) - (rightCount X p q : ℤ)|

end Green75
