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

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/36.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Green's Open Problem 36

*References:*
* [Gr24] [Green's Open Problems #36](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.36)
* [CKS05] Cohn, H., Kleinberg, R., Szegedy, B., and Umans, C. "Group-theoretic Algorithms for
  Matrix Multiplication" (Problem 4.7)
-/

section

open Filter
open scoped Pointwise

namespace Green36

/-- The simultaneous double product property [CKS05, 4.1]. -/
def SimultaneousDoubleProduct {ι H : Type*} [AddCommGroup H]
    (A B : ι → Finset H) : Prop :=
  open scoped Classical in
  (∀ i, (A i + B i).card = (A i).card * (B i).card) ∧
  (∀ i j k, i ≠ k → Disjoint (A i + B j) (A j + B k))

/-- A variant of the simultaneous double product property, as stated in [Gr24, Problem 36]. -/
def Green36Property {ι H : Type*} [AddCommGroup H]
    (A B : ι → Finset H) : Prop :=
  open scoped Classical in
  (∀ i, (A i + B i).card = (A i).card * (B i).card) ∧
  (∀ i j k, j ≠ k → Disjoint (A i + B i) (A j + B k))

-- TODO(jeangud) Add variants mentioned in [Gr24, Problem 36] comments.

end Green36
