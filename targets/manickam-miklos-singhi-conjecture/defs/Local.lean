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

/-! Ported mechanically from `FormalConjectures/Paper/ManickamMiklosSinghiConjecture.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The Manickam–Miklós–Singhi conjecture (1988)

*References:*
* [MM88] Manickam, N. and Miklós, D. (1988). "On the number of nonnegative partial sums of a
  nonnegative sum." *Colloq. Math. Soc. János Bolyai* 52, pp. 385--392.
* [MS88] Manickam, N. and Singhi, N. M. (1988). "First distribution invariants and EKR theorems."
  *J. Combin. Theory Ser. A* 48, pp. 91--103.
* [CSS14] Chowdhury, A., Sarkis, G. and Shahriari, S. (2014). "The Manickam–Miklós–Singhi
  conjectures for sets and vector spaces." *J. Combin. Theory Ser. A* 128, pp. 84--103.
  [arXiv:1309.2212](https://arxiv.org/abs/1309.2212)
* [Po15] Pokrovskiy, A. (2015). "A linear bound on the Manickam–Miklós–Singhi conjecture."
  *J. Combin. Theory Ser. A* 133, pp. 280--306. [arXiv:1308.2176](https://arxiv.org/abs/1308.2176)
-/

section

open Finset

namespace ManickamMiklosSinghiConjecture

/-- The number of `k`-element subsets of `Fin n` on which the real weights `x` have
nonnegative sum. -/
noncomputable def nonnegSubsetCount (n k : ℕ) (x : Fin n → ℝ) : ℕ :=
  ((univ : Finset (Fin n)).powersetCard k).filter (fun S => 0 ≤ ∑ i ∈ S, x i) |>.card

end ManickamMiklosSinghiConjecture
