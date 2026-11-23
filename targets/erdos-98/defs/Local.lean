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
import Defs.CombinatoricsAPBasic
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataSetTriplewise
import Defs.DataSymSym2
import Defs.FieldTheoryMilnorKTheory
import Defs.Geometry2d
import Defs.GeometryMetric
import Defs.GroupTheoryRationalClasses
import Defs.LogicEquivFinRotate

/-! Ported mechanically from `FormalConjectures/ErdosProblems/98.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 98

*References:*
- [[Er75f](https://mathscinet.ams.org/mathscinet/relay-station?mr=411984)]
  Erdős, Paul, On some problems of elementary and combinatorial geometry.
  Ann. Mat. Pura Appl. (4) (1975), 99-108.
- [[Er83c](https://mathscinet.ams.org/mathscinet/relay-station?mr=706025)]
  Erdős, Paul, Combinatorial problems in geometry.
  Math. Chronicle (1983), 35-54.
- [[Er87b](https://mathscinet.ams.org/mathscinet/relay-station?mr=910710)]
  Erdős, P., Some combinatorial and metric problems in geometry.
  Intuitive geometry (Siófok, 1985) (1987), 167-177.
- [[Er90](https://mathscinet.ams.org/mathscinet/relay-station?mr=1117038)]
  Erdős, Paul, Some of my favourite unsolved problems.
  A tribute to Paul Erdős (1990), 467-478.
- [[Er92b](https://mathscinet.ams.org/mathscinet/relay-station?mr=1275857)]
  Erdős, Paul, Some of my favourite problems in various branches of combinatorics.
  Matematiche (Catania) (1992), 231-240.
- [[EFPR93](https://mathscinet.ams.org/mathscinet/relay-station?mr=1210096)]
  Erdős, Paul and Füredi, Zoltán and Pach, János and Ruzsa, Imre Z.,
  The grid revisited. Discrete Math. (1993), 189-196.
- [[Er94b](https://mathscinet.ams.org/mathscinet/relay-station?mr=1304854)]
  Erdős, Paul, Some problems in number theory, combinatorics and combinatorial geometry.
  Math. Pannon. (1994), 261-269.
- [[Er97e](https://mathscinet.ams.org/mathscinet/relay-station?mr=1487304)]
  Erdős, Paul, Some of my favourite unsolved problems.
  Math. Japon. (1997), 527-537.
- [erdosproblems.com/98](https://www.erdosproblems.com/98)
-/

section

open Finset EuclideanGeometry Filter

namespace Erdos98

/-- $h(n)$ is the minimum number of distinct distances determined by any
$n$-point set in $\mathbb{R}^2$ in general position (no three collinear, no four
cocyclic). -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ points : Finset ℝ², points.card = n ∧
    InGeneralPosition points ∧ k = distinctDistances points}

end Erdos98
