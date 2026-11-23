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
import Defs.AlgebraOrderGroupPointwiseInterval
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsAdditiveVCDim
import Defs.CombinatoricsSetFamilyVCDim
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.ComputabilityBitstringEncoding
import Defs.ComputabilityComplexity
import Defs.DataSetDensity
import Defs.DataSetInterval
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.OrderIntervalFinsetBasic
import Defs.OrderIntervalFinsetNat

/-! Ported mechanically from `FormalConjectures/ErdosProblems/274.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 274

*References:*
* [erdosproblems.com/274](https://www.erdosproblems.com/274)
* [Wikipedia](https://en.wikipedia.org/wiki/Herzog%E2%80%93Sch%C3%B6nheim_conjecture)
* [arXiv:1803.08301](https://arxiv.org/abs/1803.08301)
* [arXiv:1803.03569](https://arxiv.org/abs/1803.03569)
* [PMC7247885](https://pmc.ncbi.nlm.nih.gov/articles/PMC7247885/)
* [arXiv:1804.11103](https://arxiv.org/abs/1804.11103)
-/

section

open scoped Pointwise Cardinal

namespace Erdos274

-- TODO(callesonne): add already proved results from the wiki page

/-- An exact covering of a group `G` is a finite collection of subgroups `{H_1, ..., H_k}` and
representative `{g_1, ..., g_k}` such that the cosets `g_iH_i` are pairwise disjoint and their
union covers `G`.

Note that this differs from `Partition (α := Subgroup G)` because the covering condition there
invokes `Subgroup.sup` which is subgroup generation and thus stronger than union. This definition
is easier to use in this context than the alternative `Partition (α := Set G)`, which lacks
subgroup definitions such as `Subgroup.index`. -/
structure Group.ExactCovering (G : Type*) [Group G] (ι : Type*) [Fintype ι] where
  parts : ι → Subgroup G
  reps : ι → G
  nonempty (i : ι) : (parts i : Set G).Nonempty
  disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun (i : ι) ↦ reps i • (parts i : Set G)
  covers : ⋃ i, reps i • (parts i : Set G) = Set.univ

end Erdos274
