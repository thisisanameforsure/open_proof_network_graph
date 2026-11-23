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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/1062.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 1062

*Reference:* [erdosproblems.com/1062](https://www.erdosproblems.com/1062)
-/

section

open Filter
open scoped Topology

namespace Erdos1062

/-- A set `A` of positive integers is fork-free if no element divides two distinct
other elements of `A`. -/
def ForkFree (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ({b | b ∈ A \ {a} ∧ a ∣ b} : Set ℕ).Subsingleton

/-- The extremal function from Erdős problem 1062: the largest size of a fork-free subset of
`{1,...,n}`. -/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard = k) n

-- TODO: Add erdos_1062.parts.i: How large can $f(n)$ be?

end Erdos1062
