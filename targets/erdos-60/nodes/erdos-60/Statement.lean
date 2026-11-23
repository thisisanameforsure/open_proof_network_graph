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
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsHypergraphBasic
import Defs.CombinatoricsHypergraphFinite
import Defs.CombinatoricsSetFamilyPropertyB

/-! Erdős problem 60: Does every graph on $n$ vertices with $>\mathrm{ex}(n;C_4)$ edges contain $\gg n^{1/2}$ many copies of $C_4$? — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/60.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open SimpleGraph Filter
open scoped Real

theorem Opn.erdos_60 :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (extremalNumber n (cycleGraph 4) < G.edgeFinset.card) →
          (c * Real.sqrt (n : ℝ) ≤ ({ H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4) }.ncard : ℝ)) := by
  sorry
