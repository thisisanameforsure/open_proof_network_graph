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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local

/-! Erdős problem 461: Let $s_t(n)$ be the $t$-smooth component of $n$ - that is, the product of all primes $p$ (with multiplicity) dividing $n$ such that $p<t$. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/461.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Erdos461

theorem Opn.erdos_461 :
    ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, c * (t : ℝ) ≤ (f n t : ℝ) := by
  sorry
