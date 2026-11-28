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
import Defs.CombinatoricsStableMarriage
import Defs.CombinatoricsStableMarriageUnbalanced
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local

/-! Pittel's stable-matching hyperbola threshold conjecture — imported from google-deepmind/formal-conjectures (FormalConjectures/Arxiv/2406.10319/StableMatchingHyperbola.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter MeasureTheory StableMarriage
open scoped Topology
open Arxiv.«2406.10319»

theorem Opn.pittel_hyperbola_threshold :
    ∃ pStar : ℕ → Set.Ioo (0 : ℝ) 1,
      let d (n : ℕ) := min (pStar n : ℝ) (1 - (pStar n : ℝ))
      (∀ᶠ (n : ℕ) in atTop, (9 / 4 : ℝ) * (Real.log n) ^ 2 / n < (pStar n : ℝ)) ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        (∀ ε > 0, Tendsto (fun n ↦
          ⨆ p : {p : unitInterval // (pStar n : ℝ) + δ * d n ≤ (p : ℝ)},
            marketLaw n p.1 (hyperbolaEvent n p.1 ε)ᶜ) atTop (𝓝 0)) ∧
        ∃ ε > 0, Tendsto (fun n ↦
          ⨆ p : {p : unitInterval // (p : ℝ) ≤ (pStar n : ℝ) - δ * d n},
            marketLaw n p.1 (hyperbolaEvent n p.1 ε)) atTop (𝓝 0) := by
  sorry
