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

/-! Erdős problem 388: Are there only finitely many solutions of $$\prod_{1\leq i\leq k_1}(m_1+i)=\prod_{1\leq j\leq k_2}(m_2+j)$$ with $k_1,k_2>3$ and $m_1+k_1\leq m_2$? — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/388.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

theorem Opn.erdos_388 :
    {(m₁, k₁, m₂, k₂) : ℕ × ℕ × ℕ × ℕ | 3 < k₁ ∧ 3 < k₂ ∧ m₁ + k₁ ≤ m₂ ∧
      ∏ i ∈ Finset.Icc 1 k₁, (m₁ + i) = ∏ j ∈ Finset.Icc 1 k₂, (m₂ + j)}.Finite := by
  sorry
