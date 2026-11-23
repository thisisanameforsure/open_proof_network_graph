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
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local

/-! The Manickam–Miklós–Singhi conjecture (1988) — imported from google-deepmind/formal-conjectures (FormalConjectures/Paper/ManickamMiklosSinghiConjecture.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Finset
open ManickamMiklosSinghiConjecture

theorem Opn.manickam_miklos_singhi_conjecture :
    ∀ (n k : ℕ), 1 ≤ k → 4 * k ≤ n → ∀ x : Fin n → ℝ, ∑ i, x i = 0 →
      (n - 1).choose (k - 1) ≤ nonnegSubsetCount n k x := by
  sorry
