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
import Defs.ComputabilityBitstringEncoding
import Defs.ComputabilityComplexity

/-! Erdős problem 663: Let $k \geq 2$, and let $q(n,k)$ denote the least prime which does not divide $\prod_{1 \leq i \leq k}(n+i)$. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/663.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter Asymptotics
open scoped BigOperators

theorem Opn.erdos_663 :
    ∀ k ≥ 2, ∃ error : ℕ → ℝ,
    error =o[atTop] (fun _ ↦ (1 : ℝ)) ∧ ∀ᶠ n in atTop,
      let P : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)
      ∃ q : ℕ, q.Prime ∧ ¬ q ∣ P ∧ (∀ p : ℕ, p.Prime → ¬ p ∣ P → q ≤ p) ∧
        (q : ℝ) < (1 + error n) * Real.log n := by
  sorry
