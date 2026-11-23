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

/-! Ported mechanically from `FormalConjectures/Wikipedia/ErdosMoser.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# The Erdős–Moser equation

For positive integers $k$ and $m$, let

$$S_k(m)=1^k+2^k+\cdots+(m-1)^k.$$

The Erdős–Moser conjecture says that $S_k(m)=m^k$ has only the solution
$(k,m)=(1,3)$.

*References:*
* [Wikipedia: Erdős–Moser equation](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Moser_equation)
* B. C. Kellner,
  [On stronger conjectures that imply the Erdős–Moser conjecture](https://arxiv.org/abs/1003.1646)
-/

section

namespace ErdosMoser

/-- The power sum $S_k(m)=\sum_{i=1}^{m-1} i^k$. -/
def powerSum (k m : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico 1 m, i ^ k

end ErdosMoser
