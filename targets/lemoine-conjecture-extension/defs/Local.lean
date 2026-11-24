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
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex

/-! Ported mechanically from `FormalConjectures/Wikipedia/Lemoine.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Lemoine's conjectures

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/%C3%89mile_Lemoine#Lemoine's_conjecture_and_extensions)
- [Ki85] Kiltinen, J. and Young P. (1985). Goldbach, Lemoine, and a Know/Don't Know Problem.
-/

section

namespace Lemoine

def OddPrime (n : ℕ) : Prop :=
  n ≠ 2 ∧ n.Prime

end Lemoine
