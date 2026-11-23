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
import Defs.NumberTheoryAdditiveComplement
import Defs.NumberTheoryMultiplicativelyIndependent

/-! Ported mechanically from `FormalConjectures/ErdosProblems/704.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 704

*References:*
- [erdosproblems.com/704](https://www.erdosproblems.com/704)
- [Da26] Davies, J., *Measurable obstructions for unmeasurable colourings*. Preprint (2026).
  [arXiv:2610.12301](https://arxiv.org/abs/2610.12301)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [FrWi81] Frankl, P. and Wilson, R. M., *Intersection theorems with geometric consequences*.
  Combinatorica (1981), 357-368.
- [LaRo72] Larman, D. G. and Rogers, C. A., *The realization of distances within sets in
  Euclidean space*. Mathematika (1972), 1-24.
- [Pr20] Prosanov, R., *A new proof of the Larman-Rogers upper bound for the chromatic number of
  the Euclidean space*. Discrete Appl. Math. (2020), 115-120.
- [Ra00] Raigorodskii, A. M., *On the chromatic number of a space*. Uspekhi Mat. Nauk (2000),
  147-148.
-/

section

open Filter
open scoped Topology

namespace Erdos704

/--
The unit distance graph $G_n$ on $\mathbb{R}^n$: two points are adjacent if and only if the
distance between them is $1$.
-/
def unitDistanceGraph (n : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin n)) where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]

end Erdos704
