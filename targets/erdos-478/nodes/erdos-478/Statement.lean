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
import Defs.ModelTheoryEncoding
import Defs.ModelTheoryReal

/-! Erdős problem 478: Let $p$ be a prime and $$A_p = \{ k! \pmod{p} : 1\leq k<p\}.$$ Is it true that $$\lvert A_p\rvert \sim (1-\tfrac{1}{e})p?$$ — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/478.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

theorem Opn.erdos_478 :
    Filter.Tendsto
      (fun p : ℕ =>
        (((Finset.Ico 1 p).image (fun k => Nat.factorial k % p)).card : ℝ) / p)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime})
      (nhds (1 - 1 / Real.exp 1)) := by
  sorry
