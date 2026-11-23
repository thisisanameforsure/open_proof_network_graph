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

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/86.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Ben Green's Open Problem 86

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.86)
- [KRS00] Konyagin, S. V., Ruzsa, I. Z. and Schlag, W., *On uniformly distributed dilates of
  finite integer sequences*. J. Number Theory 82 (2000), 165--187.
  [doi:10.1006/jnth.1999.2420](https://doi.org/10.1006/jnth.1999.2420)
- [Mo94] Montgomery, H. L., *Ten lectures on the interface between analytic number theory and
  harmonic analysis*. CBMS Regional Conference Series in Mathematics 84, American Mathematical
  Society (1994).
-/

section

open scoped Finset

namespace Green86

/--
`numInInterval A θ t` is the number of $a \in A$ such that $\theta a \pmod 1$ lies in the
interval $[t, t + 1/n)$ of $\mathbb{R}/\mathbb{Z}$, where $n = |A|$.
-/
noncomputable def numInInterval (A : Finset ℤ) (θ t : ℝ) : ℕ :=
  #{a ∈ A | Int.fract (θ * ((a : ℤ) : ℝ) - t) < 1 / (#A : ℝ)}

end Green86
