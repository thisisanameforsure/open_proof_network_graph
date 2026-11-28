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

/-! The $\frac 1 3$–$\frac 2 3$ conjecture — imported from google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/conjecture_1_3_to_2_3.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

theorem Opn.conjecture_1_3_to_2_3 :
    ∀ (P : Type) [Finite P] [PartialOrder P]
    (not_total : ¬ Std.Total (α := P) (· ≤ ·)) (total_ext : Set <| OrderHom P ℕ)
    (total_ext_def : ∀ σ, σ ∈ total_ext ↔ Set.range σ = Set.Icc 1 (Nat.card P)),
    ∃ x y : P, ({σ ∈ total_ext | σ x < σ y}.ncard / total_ext.ncard : ℚ)
      ∈ Set.Icc (1/3) (2/3) := by
  sorry
