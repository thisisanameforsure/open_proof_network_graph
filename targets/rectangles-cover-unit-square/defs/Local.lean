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

/-! Ported mechanically from `FormalConjectures/Mathoverflow/34145.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Mathoverflow 34145

Can the unit square be covered by $1/k$-by-$1/(k+1)$ rectangles (across $1 \le k$ natural)?

I am deliberately not requiring that the rotations can only be $0^\circ, 90^\circ, 180^\circ, \text{ or } 270^\circ$.

Because of indexing, since `n : ℕ` starts at 0, we change the side lengths to $1 / (n + 1)$ and
$1 / (n + 2)$, so that the first rectangle is $1/1$ by $1/2$, the second is $1/2$ by $1/3$, etc.

*Reference:* [mathoverflow/34145](https://mathoverflow.net/q/34145)
asked by user [*Kaveh*](https://mathoverflow.net/users/7507/kaveh)
-/

section

open Real MeasureTheory Measure Module
namespace Mathoverflow34145

/-- A rectangle is specified by its width, height, starting point, and rotation.
The rectangle is assumed to start in the lower left corner. For example, the unit square
$\{ (x, y) \mid 0 \le x \le 1, 0 \le y \le 1 \}$ is specified as `⟨1, 1, (0, 0), 0⟩`  -/
structure Rectangle : Type where
  width : ℝ
  height : ℝ
  start : ℝ × ℝ
  rotation : Angle

/-- A combination of a rotation and a translation to map the standard rectangle to the desired
rectangle.
-/
noncomputable def rigidMotion (start : ℝ × ℝ) (θ : Angle) (p : ℝ × ℝ) : (ℝ × ℝ) :=
  (start.1 + p.1 * θ.cos - p.2 * θ.sin, start.2 + p.1 * θ.sin + p.2 * θ.cos)

/-- A scaling to map the unit square to a standard rectangle. -/
noncomputable def scale (x y : ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) :=
  (x * p.1, y * p.2)

/-- The unit square. -/
def unitSquare : Set (ℝ × ℝ) :=
  { p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 }

/-- Converts a rectangle to a set in `ℝ × ℝ`. -/
def Rectangle.toSet (r : Rectangle) : Set (ℝ × ℝ) :=
  rigidMotion r.start r.rotation '' (scale r.width r.height '' unitSquare)

/-- The standard Lebesgue measure on `ℝ²`. -/
noncomputable abbrev lbMeasure : Measure (ℝ × ℝ) :=
  (Basis.finTwoProd ℝ).addHaar

/-- A configuration of rectangles of sides `1 / (n + 1)` and `1 / (n + 2)`. -/
structure Configuration : Type where
  rect (n : ℕ) : Rectangle
  rect_width (n : ℕ) : (rect n).width = 1 / (n + 1)
  rect_height (n : ℕ) : (rect n).height = 1 / (n + 2)

/-- A "packing" means that the interiors of any two rectangles are disjoint. -/
def Configuration.IsPacking (c : Configuration) : Prop :=
  Pairwise fun m n ↦ interior (c.rect m).toSet ∩ interior (c.rect n).toSet = ∅

end Mathoverflow34145
