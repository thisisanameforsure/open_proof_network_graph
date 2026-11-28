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
import Defs.CombinatoricsSimpleGraphDegrees
import Defs.CombinatoricsSimpleGraphEdgeColouring

/-! Erdős problem 802: Is it true that any $K_r$-free graph on $n$ vertices with average degree $t$ contains an independent set on $$\gg_r \frac{\log t}{t}n$$ many vertices? — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/802.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Real
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical

theorem Opn.erdos_802 :
    ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r →
      c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum := by
  sorry
