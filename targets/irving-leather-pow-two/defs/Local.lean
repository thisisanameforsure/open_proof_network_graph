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
import Defs.AlgebraOrderGroupPointwiseInterval
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsAdditiveVCDim
import Defs.CombinatoricsSetFamilyVCDim
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.CombinatoricsStableMarriage
import Defs.CombinatoricsStableMarriageUnbalanced
import Defs.DataSetDensity
import Defs.DataSetInterval
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.OrderIntervalFinsetBasic
import Defs.OrderIntervalFinsetNat

/-! Ported mechanically from `FormalConjectures/Paper/IrvingLeatherStableMatchings.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The Irving–Leather conjecture on stable matchings

*References:*
- [Concerning the maximum number of stable matchings in the stable marriage problem](https://core.ac.uk/download/pdf/82220141.pdf)
  by E. G. Thurber, §2 and Appendix A.
- [A recurrence giving a lower bound for stable matchings](https://oeis.org/A005154/a005154.pdf)
  by Clay Thomas, Proposition 1.

Let $M(n)$ be the maximum number of stable matchings with $n$ participants per side and complete,
strict preferences. The Irving–Leather construction has $a_k$ stable matchings at size $2^k$.
-/

section

open Filter
open scoped Topology

namespace IrvingLeather

/-- The maximum number of stable matchings over all preference profiles of size $n$. -/
noncomputable def maxStableMatchings (n : ℕ) : ℕ :=
  Finset.univ.sup (fun p : StableMarriage.Profile n ↦ StableMarriage.numStableMatchings p)

/-- The number $a_k$ of stable matchings in the Irving–Leather construction of size $2^k$. -/
def irvingLeatherCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | k + 2 => 3 * irvingLeatherCount (k + 1) ^ 2 - 2 * irvingLeatherCount k ^ 4

end IrvingLeather
