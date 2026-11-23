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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/945.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 945

*References:*
 - [erdosproblems.com/945](https://www.erdosproblems.com/945)
 - [ErMi52] Erdős, P. and Mirsky, L., The distribution of values of the divisor function {$d(n)$}. Proc. London Math. Soc. (3) (1952), 257--271.
-/

section

open Filter Real

namespace Erdos945

abbrev τ  := fun (n : ℕ) => n.divisors.card

/--
Let $F(x)$ be the maximal $k$ such that there exist $n+1, \dots, n+k \le x$
with $τ(n+1), \dots, τ(n+k)$ all distinct, where $τ(m)$ counts the divisors of $m$. -/
noncomputable def F (x : ℝ) : ℕ :=
  sSup {k | ∃ (n : ℕ), n + k ≤ x ∧ (Set.Ioc n (n + k)).InjOn τ}

-- Implementation note: we define a Prop here and below to be able to easily formulate
-- the equivalence between the two variants. Because the theorems have an unknown `answer` we
-- can't handle this with `type_of%`.
def Erdos945Prop : Prop := ∃ O : ℝ → ℝ, O =O[atTop] (1 : ℝ → ℝ) ∧ ∀ᶠ x in atTop, F x ≤ log x ^ O x

def Erdos945Constant : Prop :=
  ∃ C > (0 : ℝ),  ∀ᶠ x : ℝ in atTop,
    ∃ a b : ℕ, a ≠ b ∧
    ↑a ∈ Set.Icc x (x + log x ^ C) ∧
    ↑b ∈ Set.Icc x (x + log x ^ C) ∧
    τ a = τ b

-- TODO(firsching): show equivalence
-- TODO(firsching): add observations what follows from Cramér's conjecture and if every sufficient
-- interval contains a squarefree number.

end Erdos945
