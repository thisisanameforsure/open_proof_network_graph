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

/-! Ported mechanically from `FormalConjectures/Arxiv/math.0703548/FarrellJonesConsequences.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Algebraic consequences of the Farrell–Jones conjecture

The assembly map in the Farrell–Jones conjecture is not yet available in Mathlib. This file
states two of its algebraic consequences using projective modules and matrices over group rings:
the vanishing of the reduced projective class group and the Bass conjecture for commutative
integral domains.

*Reference:*
- [BLR08] [arxiv/math.0703548](https://arxiv.org/abs/math/0703548)
  **On the Farrell–Jones Conjecture and its applications**
  by *Arthur Bartels, Wolfgang Lück, Holger Reich*, J. Topol. 1 (2008), 57–86.
-/

section

namespace Arxiv.«math.0703548»

open scoped Classical in
/--
The value at the conjugacy class of `g` of the universal trace of a matrix over `R[G]`.

For each diagonal entry, this sums the coefficients of the elements conjugate to `g`. If the
matrix is idempotent, these values give the Hattori–Stallings rank of the projective module
represented by the matrix.
-/
noncomputable def matrixHattoriStallingsTraceAt {R : Type*} [CommRing R] {G : Type*} [Group G]
    {n : Type*} [Fintype n] (A : Matrix n n (MonoidAlgebra R G)) (g : G) : R :=
  ∑ i, (A i i).coeff.sum fun h r ↦ if IsConj h g then r else 0

end Arxiv.«math.0703548»
