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
import Defs.ModelTheoryEncoding
import Defs.ModelTheoryReal

/-! Erdős problem 312: Does there exist a constant `c > 0` such that, for any `K > 1`, whenever `A` is a sufficiently large finite multiset of integers with $\sum_{n \in A} 1/n > K$ there exists some $S \ — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/312.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

theorem Opn.erdos_312 :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (K : ℝ), 1 < K →
        ∃ (N₀ : ℕ),
          ∀ (n : ℕ) (a : Fin n → ℕ),
            (n ≥ N₀ ∧ (∑ i : Fin n, (a i : ℝ)⁻¹) > K) →
              ∃ (S : Finset (Fin n)),
                1 - Real.exp (-(c * K)) < (∑ i ∈ S, (a i : ℝ)⁻¹) ∧
                ∑ i ∈ S, (a i : ℝ)⁻¹ ≤ 1 := by
  sorry
