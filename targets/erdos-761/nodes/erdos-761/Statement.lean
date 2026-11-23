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
import Defs.CombinatoricsDigraphTournament
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local

/-! Erdős problem 761, part i: The dichromatic number of $G$, denoted by $\delta(G)$, is the minimum number $k$ of colours required such that, in any orientation of the edges of $G$, there is a $k$-colour — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/761.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Erdos761

theorem Opn.erdos_761 :
    ∀ k : ℕ, ∃ m : ℕ, ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      (m : ℕ∞) ≤ G.chromaticNumber → (k : ℕ∞) ≤ dichromaticNumber G := by
  sorry
