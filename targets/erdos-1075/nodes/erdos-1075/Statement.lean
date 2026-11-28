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

/-! Erdős problem 1075: Let $r\geq 3$. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1075.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter Asymptotics

theorem Opn.erdos_1075 :
    ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, (r : ℝ)⁻¹ ^ r < c ∧
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, ∀ H : Finset (Finset (Fin n)),
        H.IsUniform r → (1 + ε) * ((n : ℝ) / r) ^ r ≤ H.card →
          ∃ S : Finset (Fin n), S.card = m n ∧
            c * (S.card : ℝ) ^ r ≤ (H.hypergraphInduce S).card := by
  sorry
