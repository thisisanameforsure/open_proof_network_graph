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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/624.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 624

*Reference:* [erdosproblems.com/624](https://www.erdosproblems.com/624)

-/

section
namespace Erdos624

open Filter Finset

/--
The condition that an integer `m` ensures the existence of a function `f` covering `Fin n`
for all large enough subsets `Y`.
The property is invariant under bijection, so we use a representative `Fin n` for a finite set
of size `n`.
-/
def ExistsEventuallySurjective (n m : ℕ) : Prop :=
  ∃ (f : Finset (Fin n) → Fin n),
    ∀ (Y : Finset (Fin n)), #Y ≥ m →
      Y.powerset.image f = Finset.univ

/--
Let $H(n)$ be the minimum integer $m$ such that there is a function $f: \mathcal{P}(X) \to X$
where $X$ is a finite set of size $n$, such that for every subset $Y \subseteq X$ with $|Y| \ge m$,
the set $\{f(A) : A \subseteq Y\}$ covers $X$.
-/
noncomputable def H (n : ℕ) : ℕ :=
  if 0 < n then
    sInf {m : ℕ | ExistsEventuallySurjective n m}
  else 0

end Erdos624
