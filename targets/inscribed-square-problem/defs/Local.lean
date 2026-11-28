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
import Defs.DataSetTriplewise
import Defs.DataSymSym2
import Defs.FieldTheoryMilnorKTheory
import Defs.Geometry2d
import Defs.GeometryMetric
import Defs.GroupTheoryRationalClasses
import Defs.LogicEquivFinRotate

/-! Ported mechanically from `FormalConjectures/Wikipedia/InscribedSquare.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Inscribed square problem

The *inscribed square problem* or *Toeplitz conjecture* asks whether every Jordan curve (i.e. simple
close curve in ℝ²) admits an inscribed square, i.e. a square whose vertices all lie on the curve.
There are several open and solved variants of this conjecture.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Inscribed_square_problem)
 - [A Survey on the Square Peg Problem](https://www.researchgate.net/publication/274622766_A_Survey_on_the_Square_Peg_Problem)
   by *Benjamin Matschke*
 - [arxiv/2005.09193](https://arxiv.org/abs/2005.09193)
-/

section

open Topology ContDiff Manifold
open scoped EuclideanGeometry

namespace InscribedSquare

/-- Four points `a b c d` in the plane form a rectangle with `a` opposite to `c` iff the line
segments from `a` to `c` and from `b` to `d` have both the same length and the same midpoint, acting
as the diagonals of the rectangle. We also require the rectangle to be nondegenerate and have a
given aspect ratio `ratio : ℝ`. -/
structure IsRectangle (a b c d : ℝ²) (ratio : ℝ) : Prop where
  diagonal_midpoints_eq : a + c = b + d
  diagonal_lengths_eq : dist a c = dist b d
  a_ne_b : a ≠ b
  b_ne_c : b ≠ c
  has_ratio : (dist a b) / (dist b c) = ratio

end InscribedSquare
