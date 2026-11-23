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
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.DataSetTriplewise
import Defs.DataSymSym2
import Defs.Geometry2d
import Defs.GeometryMetric
import Defs.LogicEquivFinRotate

/-! Ported mechanically from `FormalConjectures/Wikipedia/RationalDistanceProblem.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Rational distance problem

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Unit_square#Rational_distance_problem)
- [mathoverflow/418260](https://mathoverflow.net/questions/418260/)
asked by user [Yuan Yang](https://mathoverflow.net/users/177957/yuan-yang)
- D19 in [Unsolved Problems in Number Theory](https://doi.org/10.1007/978-0-387-26677-0)
by *Richard K. Guy*
-/

section

namespace RationalDistanceProblem

open EuclideanGeometry

def UnitSquareCorners : Fin 4 → ℝ² :=
  ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]]

end RationalDistanceProblem
