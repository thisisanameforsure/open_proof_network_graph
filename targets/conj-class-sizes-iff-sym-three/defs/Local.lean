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
import Defs.CombinatoricsAPBasic
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Paper/ConjugacyClassSizes.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The $S_3$-conjecture (conjugacy classes of distinct sizes)

*References:*
* W. Zhou, I. Gorshkov, *On $\{2,3,5\}$-groups with conjugacy classes of distinct sizes*,
  [arXiv:2606.22244](https://arxiv.org/abs/2606.22244) (2026).
* F. M. Markel, *Groups with many conjugate elements*, J. Algebra **26** (1973), 69–74.
  (Origin of the $S_3$-conjecture.)
* R. Knörr, W. Lempken, B. Thielcke, *The $S_3$-conjecture for solvable groups*,
  Israel J. Math. **91** (1995), 61–76.
* J. Zhang, *Finite groups with many conjugate elements*, J. Algebra **170** (1994), 608–624.
* Z. Arad, M. Muzychuk, A. Oliver, *On groups with conjugacy classes of distinct sizes*,
  J. Algebra **280** (2004), 537–576.
* [Conjugacy class](https://en.wikipedia.org/wiki/Conjugacy_class)

A finite group in which distinct conjugacy classes have distinct cardinalities is called an
*anti-homogeneous* group (or *ah-group*). The symmetric group $S_3$ is an ah-group: its three
conjugacy classes have sizes $1$, $2$, and $3$. Markel's **$S_3$-conjecture** (1973) asserts that,
up to isomorphism, $S_3$ is the only nontrivial finite ah-group. The conjecture has been proved
for all solvable groups (independently by Zhang and by Knörr–Lempken–Thielcke), but the general
non-solvable case remains open.
-/

section

namespace ConjugacyClassSizes

open ConjClasses

/--
The cardinality of the conjugacy class `c`.
-/
noncomputable def conjClassCard {G : Type*} [Monoid G] (c : ConjClasses G) : ℕ :=
  Nat.card c.carrier

/--
A finite group `G` satisfies `HasDistinctConjClassSizes` if the map assigning to each conjugacy class the
cardinality of its carrier is injective, i.e. distinct conjugacy classes have distinct sizes.

Such a group is called an *anti-homogeneous group* (or *ah-group*).
-/
def HasDistinctConjClassSizes (G : Type*) [Group G] [Fintype G] : Prop :=
  Function.Injective (conjClassCard (G := G))

end ConjugacyClassSizes
