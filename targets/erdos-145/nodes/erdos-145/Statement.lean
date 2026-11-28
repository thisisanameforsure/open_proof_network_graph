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
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataNatFactorizationBasic
import Defs.DataNatSquarefree
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local
import Defs.TopologyCardinalInvariants

/-! Erdős problem 145: Let $s_1 < s_2 < \cdots$ be the sequence of squarefree numbers. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/145.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter
open scoped Topology
open Erdos145

theorem Opn.erdos_145 :
    ∀ α ≥ (0 : ℝ), ∃ β : ℝ,
      atTop.Tendsto (fun x : ℝ ↦ 1 / x * ∑ n ∈ A x, (s (n + 1) - s n : ℝ) ^ α) (𝓝 β) := by
  sorry
