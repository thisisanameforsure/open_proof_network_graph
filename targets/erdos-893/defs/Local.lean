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
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/893.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 893

*References:*
- [erdosproblems.com/893](https://www.erdosproblems.com/893)
- [KoLu25] V. Kovač and F. Luca, On the number of divisors of Mersenne numbers. arXiv:2506.04883 (2025).
-/

section

open Filter Finset
open scoped ArithmeticFunction.sigma

namespace Erdos893

/--
Definition of function $f(n) := \sum_{1\leq k\leq n}\tau(2^k-1)$.
Here $\tau$ is the divisor counting function, which is `σ 0` in mathlib.
-/
def f (n : ℕ) : ℕ :=  ∑ k ∈ Finset.Icc 1 n, σ 0 (2^k - 1)

end Erdos893
