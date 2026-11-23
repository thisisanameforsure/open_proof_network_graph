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

/-! Erdős problem 665: A pairwise balanced design for $\{1,\ldots,n\}$ is a collection of sets $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ such that $2\leq \lvert A_i\rvert <n$ and every pair of distinct ele — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/665.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter Asymptotics

theorem Opn.erdos_665 :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∃ H : Finset (Finset (Fin n)), H.IsPairwiseBalancedDesign ∧
      ∀ e ∈ H, e.card < n ∧ Real.sqrt n - C < e.card := by
  sorry
