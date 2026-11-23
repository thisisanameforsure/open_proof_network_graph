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
import Defs.CombinatoricsSimpleGraphEdgeColouring
import Defs.CombinatoricsSimpleGraphRamsey

/-! Erdős problem 544, part i: Show that $$R(3,k+1)-R(3,k)\to\infty$$ as $k\to \infty$. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/544.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter

theorem Opn.erdos_544 :
    Tendsto (fun k : ℕ ↦ (SimpleGraph.classicalRamsey 3 (k + 1) : ℝ) -
      (SimpleGraph.classicalRamsey 3 k : ℝ)) atTop atTop := by
  sorry
