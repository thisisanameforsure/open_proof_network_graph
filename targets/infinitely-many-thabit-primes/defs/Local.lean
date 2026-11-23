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
import Defs.NumberTheoryAmicable

/-! Ported mechanically from `FormalConjectures/Wikipedia/ThabitNumber.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Thabit numbers and Thabit primes

For $n \ge 0$, the $n$-th *Thabit number* (of the first kind) is $K_n = 3 \cdot 2^n - 1$. In the
ninth century, Thābit ibn Qurra proved that whenever $n \ge 2$ makes $p = K_{n-1}$, $q = K_n$, and
$r = 9 \cdot 2^{2n - 1} - 1$ simultaneously prime, the integers $2^n p q$ and $2^n r$ form an
amicable pair (`IsAmicable`). Whether infinitely many Thabit primes exist, and whether Thābit ibn
Qurra's rule produces any amicable pair beyond the three known exponents $n = 2, 4, 7$ [Bo72, Gu04],
remain open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Thabit_number)
- [OEIS A055010](https://oeis.org/A055010)
- [OEIS A007505](https://oeis.org/A007505)
- [OEIS A002235](https://oeis.org/A002235)
- [Bo72] Borho, W. (1972). *On Thabit ibn Kurrah's formula for amicable numbers*, Math. Comp. 26
  (118), 571--578.
- [Gu04] Guy, R. K. (2004). *Unsolved Problems in Number Theory*, 3rd ed., Problem B4, Springer,
  New York. https://doi.org/10.1007/978-0-387-26677-0
-/

section

namespace ThabitNumber

/-- The $n$-th **Thabit number** of the first kind, $K_n = 3 \cdot 2^n - 1$
([OEIS A055010](https://oeis.org/A055010)). -/
def thabitNumber (n : ℕ) : ℕ := 3 * 2 ^ n - 1

end ThabitNumber
