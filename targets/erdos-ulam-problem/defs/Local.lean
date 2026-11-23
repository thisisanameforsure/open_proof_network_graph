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
import Defs.ComputabilityTuringMachineBusyBeavers
import Defs.ComputabilityTuringMachineNotation
import Defs.ComputabilityTuringMachinePostTuringMachine
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Wikipedia/ErdosUlamProblem.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The Erdős–Ulam problem

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Ulam_problem)
* [Ul60] Ulam, S. M. (1960). *A Collection of Mathematical Problems.* Interscience, p. 40.
* [SdZ10] Solymosi, J. and de Zeeuw, F. (2010). "On a question of Erdős and Ulam."
  *Discrete Comput. Geom.* 43, pp. 393--401. [arXiv:0806.3095](https://arxiv.org/abs/0806.3095)
* [Ta14] Tao, T. (2014). "The Erdős–Ulam problem, varieties of general type, and the
  Bombieri–Lang conjecture." Blog post,
  [terrytao.wordpress.com](https://terrytao.wordpress.com/2014/12/20/the-erdos-ulam-problem-varieties-of-general-type-and-the-bombieri-lang-conjecture/)
* [AE45] Anning, N. H. and Erdős, P. (1945). "Integral distances." *Bull. Amer. Math. Soc.* 51,
  pp. 598--600.
-/

section

open EuclideanSpace

namespace ErdosUlamProblem

/-- A set of points of the plane has **pairwise rational distances** if the distance between any
two of its points is a rational number. -/
def PairwiseRationalDistances (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, dist p q = (r : ℝ)

end ErdosUlamProblem
