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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local
import Defs.NumberTheoryLacunary

/-! Erdős problem 996: Does there exists a positive constant `C` such that for all `f ∈ L²[0,1]` and all lacunary sequences `n`, if `‖f - fₖ‖₂ = O(1 / log log log k ^ C)`, then for almost every `x`, `lim  — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/996.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open Erdos996

theorem Opn.erdos_996 :
    ∃ (C : ℝ), 0 < C ∧ ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsLacunary n →
    (fun k => (eLpNorm (⇑f - fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k => 1 / (log (log (log k))) ^ C)
    →
    ∀ᵐ x, Tendsto (fun N => (∑ k ∈ .range N, f (n k • x)) / N) atTop
    (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  sorry
