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
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataNatFactorizationBasic
import Defs.DataNatSquarefree
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.TopologyCardinalInvariants

/-! Ported mechanically from `FormalConjectures/ErdosProblems/145.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 145

*Reference:* [erdosproblems.com/145](https://www.erdosproblems.com/145)
-/

section

namespace Erdos145

open Filter
open scoped Topology

/-- Let $s_1 < s_2 < \cdots$ be the sequence of squarefree numbers. -/
noncomputable abbrev s (n : ℕ) : ℕ := Nat.nth Squarefree n

/-- Let $A(x)$ denote the set of indices $n$ for which $s_n \leq x$. -/
noncomputable abbrev A (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).preimage s (Nat.nth_injective Nat.squarefree_infinite).injOn

end Erdos145
