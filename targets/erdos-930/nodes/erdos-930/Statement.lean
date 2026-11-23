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
import Defs.Local

/-! Erdős problem 930: Is it true that, for every $r$, there is a $k$ such that if $I_1,\ldots,I_r$ are disjoint intervals of consecutive integers, all of length at least $k$, then $$ \prod_{1\leq i\leq r — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/930.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Finset
open Erdos930

theorem Opn.erdos_930 :
    ∀ r > 0, ∃ k, ∀ I₁ I₂ : Fin r → ℕ,
      (∀ i : Fin r, 0 < I₁ i ∧ I₁ i + k ≤ I₂ i + 1) →
        (∀ i j : Fin r, i < j → I₂ i < I₁ j) →
          ¬ IsPower (∏ i : Fin r, ∏ m ∈ Icc (I₁ i) (I₂ i), m) := by
  sorry
