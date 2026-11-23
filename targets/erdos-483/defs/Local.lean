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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/483.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 483

*References:*
- [erdosproblems.com/483](https://www.erdosproblems.com/483)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl.
  (1961), 221-254, p.233, Problem 20.
-/

section

namespace Erdos483

/-- A monochromatic solution to $a+b=c$ in $\{1,\ldots,N\}$.
Index $i$ represents $i+1$, and equal summands are allowed. -/
def HasTriple {k N : ℕ} (χ : Fin N → Fin k) : Prop :=
  ∃ a b c : Fin N, (a.val + 1) + (b.val + 1) = c.val + 1 ∧
    χ a = χ b ∧ χ b = χ c

/-- Every colouring of $\{1,\ldots,N\}$ with at most $k$ colours has a Schur triple. -/
def Forces (k N : ℕ) : Prop := ∀ χ : Fin N → Fin k, HasTriple χ

end Erdos483
