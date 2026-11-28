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

/-! Ported mechanically from `FormalConjectures/Paper/BurningNumberConjecture.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The burning number conjecture

*References:*
* [BJR16] Bonato, A., Janssen, J., and Roshanbin, E. (2016). "How to burn a graph."
  *Internet Math.* 12, pp. 85--100.
  [arXiv:1507.06524](https://arxiv.org/abs/1507.06524)
* [NT24] Norin, S. and Turcotte, J. (2024). "The burning number conjecture holds
  asymptotically." *J. Combin. Theory Ser. B* 168, pp. 208--235.
  [arXiv:2207.04035](https://arxiv.org/abs/2207.04035)
-/

section

namespace BurningNumberConjecture

variable {V : Type*}

/-- The ball-cover condition for burning a graph: every vertex is reachable from some
centre `x i` at distance at most `k - 1 - i`. The centres may repeat or already be burning
when their round starts. For finite graphs, the least such `k` is the usual burning number
[BJR16, Corollary 3]. -/
def IsBurningSequence (G : SimpleGraph V) {k : ℕ} (x : Fin k → V) : Prop :=
  ∀ v, ∃ i, G.Reachable (x i) v ∧ G.dist (x i) v + (i : ℕ) < k

/-- The **burning number** `b(G)`: the least number of rounds needed to burn every vertex
of `G`. -/
noncomputable def burningNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ x : Fin k → V, IsBurningSequence G x}

end BurningNumberConjecture
