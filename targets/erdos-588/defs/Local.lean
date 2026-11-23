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
import Defs.DataSetTriplewise
import Defs.DataSymSym2
import Defs.FieldTheoryMilnorKTheory
import Defs.Geometry2d
import Defs.GeometryMetric
import Defs.GroupTheoryRationalClasses
import Defs.LogicEquivFinRotate

/-! Ported mechanically from `FormalConjectures/ErdosProblems/588.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 588

*References:*
- [erdosproblems.com/588](https://www.erdosproblems.com/588)
- [BGS74] Burr, Stefan A. and Grünbaum, Branko and Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata (1974), 397-424.
- [Er84] Erdős, P., *Research problems*. Period. Math. Hungar. (1984), 101-103.
- [FuPa84] Füredi, Z. and Palásti, I., *Arrangements of lines with a large number of
  triangles*. Proc. Amer. Math. Soc. (1984), 561-566.
- [Gr76] Grünbaum, Branko, *New views on some old questions of combinatorial geometry*.
  Colloquio Internazionale sulle Teorie Combinatorie (Roma, 1973), Tomo I (1976), 451-468.
- [Ka63] Kárteszi, F., *Sylvester egy tételéről és Erdős egy sejtéséről*. Matematikai Lapok
  (1963), 3-10.
- [SoSt13] Solymosi, József and Stojaković, Miloš, *Many collinear $k$-tuples with no $k+1$
  collinear points*. Discrete Comput. Geom. (2013), 811-820.
-/

section

open EuclideanGeometry Filter Asymptotics

namespace Erdos588

/--
`numLinesWithPointsMax k n` is $f_k(n)$: the maximum number of lines containing exactly $k$
points among all sets $S$ of $n$ points in $\mathbb{R}^2$ with no $k + 1$ points on a line.

Since $S$ has no $k + 1$ points on a line, the lines with at least $k$ points of $S$ are exactly
the lines with exactly $k$ points of $S$. The definition follows Erdős Problem 101 (the case
$k = 4$).
-/
noncomputable def numLinesWithPointsMax (k n : ℕ) : ℕ :=
  sSup {((linesWithPointsFor k S).ncard) | (S : Set ℝ²)
    (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor (k + 1) S)}

end Erdos588
