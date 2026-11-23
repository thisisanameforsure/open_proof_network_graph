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
import Defs.AnalysisHasGaps
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.TopologyAlgebraInfiniteSumGroup
import Defs.TopologyAlgebraInfiniteSumOrder

/-! Erdős problem 517: If `f(z) = ∑ aₖzⁿₖ` is an entire function (with `aₖ ≠ 0` for all `k`) such that `nₖ / k → ∞`, is it true that `f` assumes every value infinitely often? — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/517.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Set Filter Topology

theorem Opn.erdos_517 :
    ∀ {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : HasFabryGaps n)
    {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (z : ℂ),
    {x : ℂ | f x = z}.Infinite := by
  sorry
