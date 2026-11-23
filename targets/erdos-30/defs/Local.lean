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
import Defs.CombinatoricsAPBasic
import Defs.CombinatoricsBasic
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/30.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 30

*References:*
- [erdosproblems.com/30](https://www.erdosproblems.com/30)
- [ErTu41] Erdős, P. and Turán, P., *On a problem of Sidon in additive number theory, and on
  some related problems*. J. London Math. Soc. 16 (1941), 212-215.
- [Li69] Lindström, B., *An inequality for $B_2$-sequences*. J. Combinatorial Theory 6 (1969),
  211-212.
- [Si38] Singer, J., *A theorem in finite projective geometry and some applications to number
  theory*. Trans. Amer. Math. Soc. 43 (1938), 377-385.
- [BFR23] Balogh, J., Füredi, Z. and Roy, S., *An upper bound on the size of Sidon sets*.
  Amer. Math. Monthly 130 (2023), 437-445.
- [OB22] O'Bryant, K., *On the size of finite Sidon sets*.
  [arXiv:2207.07800](https://arxiv.org/abs/2207.07800) (2022).
- [CHO25] Carter, D., Hunter, Z. and O'Bryant, K., *On the diameter of finite Sidon sets*.
  Acta Math. Hungar. 175 (2025), 108-126.

See also [Ben Green's Open Problem 31](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)
(formalised in `FormalConjectures/GreensOpenProblems/31.lean`).
-/

section

namespace Erdos30

/--
Let $h(N)$ be the maximum size of a Sidon set in $\{1, \dots, N\}$.
-/
noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)

open Filter
open scoped Asymptotics Pointwise

end Erdos30
