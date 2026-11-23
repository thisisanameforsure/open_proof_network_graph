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
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsRamsey

/-! Erdős problem 564: Let $R_3(n)$ be the minimal $m$ such that if the edges of the $3$-uniform hypergraph on $m$ vertices are $2$-coloured then there is a monochromatic copy of the complete $3$-uniform  — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/564.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Combinatorics Real Filter

theorem Opn.erdos_564 :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n := by
  sorry
