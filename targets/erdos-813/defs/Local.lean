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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/813.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 813

*References:*
- [erdosproblems.com/813](https://www.erdosproblems.com/813)
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [BuSu23] Bucić, M. and Sudakov, B., *Large independent sets from local considerations*.
  Combinatorica 43 (2023), 505-546. [arXiv:2007.03667](https://arxiv.org/abs/2007.03667)
-/

section

open Filter Asymptotics

namespace Erdos813

/--
Every set of $7$ vertices of `G` contains a triangle, that is, three pairwise adjacent
vertices. For $n < 7$ there is no such set, so the condition is vacuous.
-/
def EverySevenHasTriangle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), S.card = 7 → ∃ t ⊆ S, G.IsNClique 3 t

/--
`h n` is $h(n)$: the smallest clique number of a graph on $n$ vertices in which every set of
$7$ vertices contains a triangle. The complete graph satisfies the condition, so the set is
never empty and `sInf` is a true minimum.
-/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ G : SimpleGraph (Fin n), EverySevenHasTriangle G ∧ G.cliqueNum = k}

end Erdos813
