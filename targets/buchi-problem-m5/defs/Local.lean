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

/-! Ported mechanically from `FormalConjectures/Wikipedia/Buchi.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Büchi's problem

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/B%C3%BCchi%27s_problem)
-/

section

namespace Buchi

/-- `IsBuchi M` asserts that whenever `M` consecutive values `(x + n)² + a` (for
`n = 0, …, M - 1`) are all perfect squares, then `a` must be `0`. -/
def IsBuchi (M : ℕ) : Prop :=
  ∀ x a : ℤ, (∀ n ∈ Finset.range M, IsSquare ((x + (n : ℤ)) ^ 2 + a)) → a = 0

end Buchi
