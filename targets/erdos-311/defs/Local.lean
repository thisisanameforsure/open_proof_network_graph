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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/311.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 311

*References:*
- [erdosproblems.com/311](https://www.erdosproblems.com/311)
- [ErGr80] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980), p. 40.
-/

section

namespace Erdos311

open Finset Filter Topology

/--
`delta N` is the minimal non-zero value of $\lvert 1-\sum_{n\in A}\frac{1}{n}\rvert$ as $A$
ranges over all subsets of $\{1,\ldots,N\}$. The empty set gives the value $1$, so the set
below is nonempty for every $N$.
-/
noncomputable def delta (N : ℕ) : ℝ :=
  sInf {x : ℝ | x ≠ 0 ∧ ∃ A ⊆ Icc 1 N, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|}

end Erdos311
