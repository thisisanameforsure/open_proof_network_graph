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
import Defs.CombinatoricsSimpleGraphDegrees
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Wikipedia/GyarfasSumnerConjecture.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The Gyárfás–Sumner conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Gy%C3%A1rf%C3%A1s%E2%80%93Sumner_conjecture)
* [Gy75] Gyárfás, A. (1975). "On Ramsey covering-numbers." *Infinite and finite sets*,
  Colloq. Math. Soc. János Bolyai 10, pp. 801--816.
* [Su81] Sumner, D. P. (1981). "Subtrees of a graph and the chromatic number." *The theory
  and applications of graphs (Kalamazoo, 1980)*, Wiley, pp. 557--576.
* [Gy87] Gyárfás, A. (1987). "Problems from the world surrounding perfect graphs."
  *Zastos. Mat.* 19, pp. 413--441.
* [KP94] Kierstead, H. A. and Penrice, S. G. (1994). "Radius two trees specify χ-bounded
  classes." *J. Graph Theory* 18, pp. 119--129.
* [SS20] Scott, A. and Seymour, P. (2020). "A survey of χ-boundedness." *J. Graph Theory* 95,
  pp. 473--504. [arXiv:1812.07500](https://arxiv.org/abs/1812.07500)
-/

section

open SimpleGraph

namespace GyarfasSumnerConjecture

/-- A class of graphs given by a forbidden induced subgraph `T` is **χ-bounded by `f`** if every
finite graph `G` with no induced copy of `T` satisfies `χ(G) ≤ f(ω(G))`. -/
def IsChiBoundedBy {W : Type} (T : SimpleGraph W) (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ¬ SimpleGraph.IsIndContained T G → G.chromaticNumber ≤ f G.cliqueNum

end GyarfasSumnerConjecture
