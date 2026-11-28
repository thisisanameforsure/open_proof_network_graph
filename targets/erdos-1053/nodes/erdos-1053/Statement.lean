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
import Defs.NumberTheoryPerfectNumber

/-! Erdős problem 1053: Call a number $k$-perfect if $\sigma(n)=kn$, where $\sigma(n)$ is the sum of the divisors of $n$. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1053.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open ArithmeticFunction Filter
open scoped ArithmeticFunction.sigma

theorem Opn.erdos_1053 :
    (fun n : ℕ ↦ (σ 1 n : ℝ) / (n : ℝ)) =o[atTop ⊓ 𝓟 {n : ℕ | ∃ k, Nat.IsPerfectFor n 1 k}]
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) := by
  sorry
