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
import Defs.CombinatoricsHypergraphExtremal
import Defs.CombinatoricsHypergraphFinite
import Defs.CombinatoricsSetFamilyPropertyB

/-! Erdős problem 1178: For $r\geq 3$ let $d_r(e)$ be the minimal $d$ such that $$\mathrm{ex}_r(n,\mathcal{F})=o(n^2),$$ where $\mathcal{F}$ is the family of $r$-uniform hypergraphs on $d$ vertices with $ — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1178.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter Asymptotics

theorem Opn.erdos_1178 :
    ∀ r e : ℕ, 3 ≤ r → 3 ≤ e →
    Hypergraph.sparseConfigurationThreshold r e = (((r - 2) * e + 3 : ℕ) : ℕ∞) := by
  sorry
