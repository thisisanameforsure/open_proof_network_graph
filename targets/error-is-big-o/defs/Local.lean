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
import Defs.DataSetTriplewise
import Defs.DataSymSym2
import Defs.FieldTheoryMilnorKTheory
import Defs.Geometry2d
import Defs.GeometryMetric
import Defs.GroupTheoryRationalClasses
import Defs.LogicEquivFinRotate

/-! Ported mechanically from `FormalConjectures/Wikipedia/GaussCircleProblem.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Gauss circle problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Gauss_circle_problem)
-/

section

open Filter

open scoped EuclideanGeometry Real Topology

/-  # Gauss Circle Problem

Consider a circle in $\mathbb{R}^2$ with center at the origin and radius $r\geq 0$.
Gauss's circle problem asks how many points there are inside this circle of the form
$(m, n)$ where $m$ and $n$ are both integers. Equivalently, how many pairs of integers
$m$ and $n$ are there such that
$$
  m^2 + n^2 \leq r^2.
$$
-/

namespace GaussCircleProblem

/--
Let $N(r)$ be the number of points $(m, n)$ within a circle of radius $r$,
where $m$ and $n$ are both integers.
-/
noncomputable abbrev N (r : ℝ) : ℕ :=
  { (m, n) : ℤ × ℤ | !₂[↑m, ↑n] ∈ Metric.closedBall (0 : ℝ²) r }.ncard

/--
Let $E(r)$ be the error term between the number of integral points inside the circle and the
area of the circle; that is $N(r) = \pi r^2 + E(r)$.
-/
noncomputable abbrev E (r : ℝ) : ℝ := N r - π * r ^ 2

end GaussCircleProblem
