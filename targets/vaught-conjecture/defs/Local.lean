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

/-! Ported mechanically from `FormalConjectures/Wikipedia/VaughtConjecture.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Vaught conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Vaught_conjecture)
-/

section

namespace VaughtConjecture

open FirstOrder.Language

/-- The number of countable models of some L-Theory T up to isomorphism -/
def numberOfCountableModels {L : FirstOrder.Language} (T : L.Theory) : Cardinal :=
  Cardinal.mk (Quotient (Setoid.comap
    (fun (model : {mt : T.ModelType // Countable mt.Carrier}) ↦
    CategoryTheory.Bundled.mk model.val.Carrier model.val.struc)
    equivSetoid))

end VaughtConjecture
