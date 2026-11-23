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
import Defs.DataSetTriplewise
import Defs.DataSymSym2
import Defs.FieldTheoryMilnorKTheory
import Defs.Geometry2d
import Defs.GeometryMetric
import Defs.GroupTheoryRationalClasses
import Defs.Local
import Defs.LogicEquivFinRotate

/-! Erdős problem 99: For sufficiently large n, is it the case that any set of n points with minimum distance $1$ that minimizes diameter must contain an equilateral triangle of side length 1? — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/99.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Set Metric EuclideanGeometry
open Erdos99

theorem Opn.erdos_99 :
    ∀ᶠ n in Filter.atTop, ∀ A : Finset ℝ²,
      A.card = n → HasMinDist1 A →
      (IsMinOn (fun B: Finset ℝ² => diam (B : Set ℝ²)) {B : Finset ℝ² | B.card = n ∧ HasMinDist1 B} A) →
      ∃ᵉ (p ∈ A) (q ∈ A) (r ∈ A), FormsEquilateralTriangle p q r := by
  sorry
