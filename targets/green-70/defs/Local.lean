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

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/70.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Ben Green's Open Problem 70

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.70)
- [ABBCDHKLPW11] Abel, Z., Ballinger, B., Bose, P., Collette, S., Dujmović, V., Hurtado, F.,
  Kominers, S. D., Langerman, S., Pór, A. and Wood, D. R., *Every large point set contains many
  collinear points or an empty pentagon*. Graphs Combin. 27 (2011), 47-60.
  [arXiv:0904.0262](https://arxiv.org/abs/0904.0262)
- [KPW05] Kára, J., Pór, A. and Wood, D. R., *On the chromatic number of the visibility graph of
  a set of points in the plane*. Discrete Comput. Geom. 34 (2005), 497-506.
  [doi:10.1007/s00454-005-1177-z](https://doi.org/10.1007/s00454-005-1177-z)
- [PoWo10] Pór, A. and Wood, D. R., *On visibility and blockers*. J. Comput. Geom. 1 (2010),
  29-40. [arXiv:0912.1150](https://arxiv.org/abs/0912.1150)
-/

section

open scoped Finset

namespace Green70

/-- `HasCollinear k P` says that some $k$ points of `P` lie on a line. -/
def HasCollinear (k : ℕ) (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ S ⊆ P, #S = k ∧ Collinear ℝ (S : Set (ℝ × ℝ))

/--
`Visible P u v` says that the open segment between `u` and `v` contains no point of `P`. For
$u \neq v$ in `P` this means that `u` and `v` see each other: the segment joining them contains no
other point of `P`.
-/
def Visible (P : Finset (ℝ × ℝ)) (u v : ℝ × ℝ) : Prop :=
  ∀ w ∈ P, w ∉ openSegment ℝ u v

/--
`HasMutuallyVisible ℓ P` says that `P` contains $\ell$ mutually visible points: a subset `S` of
$\ell$ points such that any two distinct points of `S` see each other, with respect to all of `P`.
-/
def HasMutuallyVisible (ℓ : ℕ) (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ S ⊆ P, #S = ℓ ∧ (S : Set (ℝ × ℝ)).Pairwise (Visible P)

/--
`HasEmptyPentagon P` says that `P` contains an empty pentagon (a $5$-hole): five points of `P` in
strictly convex position, that is, none of them lies in the convex hull of the other four, such
that the convex hull of the five points contains no other point of `P`.
-/
def HasEmptyPentagon (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ S ⊆ P, #S = 5 ∧ ConvexIndependent ℝ ((↑) : ↥(S : Set (ℝ × ℝ)) → ℝ × ℝ) ∧
    ∀ p ∈ P, p ∈ convexHull ℝ (S : Set (ℝ × ℝ)) → p ∈ S

end Green70
