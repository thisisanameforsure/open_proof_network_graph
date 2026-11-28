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

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/28.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Green's Open Problem 28

References:
- [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.28)
- [Mathoverflow/339137](https://mathoverflow.net/questions/339137/why-do-polynomials-with-coefficients-0-1-like-to-have-only-factors-with-0-1) asked by user [Sil](https://mathoverflow.net/users/136794/sil)
- [MathStackexchange/3325163](https://math.stackexchange.com/questions/3325163/) asked by user [Emmanuel Amiot](https://math.stackexchange.com/users/403309/emmanuel-amiot)
-/

section

namespace Green28

/-- True if a PMF on $\mathbb{Z}$ is uniformly distributed on its support. -/
def IsUniformOnSupport (X : PMF ℤ) : Prop :=
  ∃ (s : Finset ℤ) (hs : s.Nonempty), X = PMF.uniformOfFinset s hs

/--
The discrete convolution of two PMFs on $\mathbb{Z}$, representing the distribution of the sum of
two independent random variables.
-/
noncomputable def indepSum (X Y : PMF ℤ) : PMF ℤ := do
  let x ← X
  let y ← Y
  PMF.pure (x + y)

end Green28
