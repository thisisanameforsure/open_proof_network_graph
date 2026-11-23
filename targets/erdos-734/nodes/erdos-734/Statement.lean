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

/-! Erdős problem 734: Find, for all large $n$, a non-trivial pairwise balanced block design $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ such that, for all $t$, there are $O(n^{1/2})$ many $i$ such that $\lv — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/734.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter Asymptotics

theorem Opn.erdos_734 :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∃ H : Finset (Finset (Fin n)), H.IsPairwiseBalancedDesign ∧
      (∀ e ∈ H, e.card < n) ∧ ∀ t : ℕ,
        ({e ∈ H | e.card = t}.card : ℝ) ≤ C * Real.sqrt n := by
  sorry
