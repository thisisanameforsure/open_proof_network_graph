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
import Defs.NumberTheoryNormalNumber

/-! Ported mechanically from `FormalConjectures/Wikipedia/AlgebraicNormality.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Normality of Irrational Algebraic Numbers

It is unknown whether every irrational algebraic real number is normal in any integer base.
Here a real number is *normal in base* $b$ if, for every $k \ge 1$, every string of $k$ digits
appears in its base-$b$ expansion with asymptotic frequency $1/b^k$.
The stronger conjecture that every irrational algebraic real number is absolutely normal is stated
separately: normality in one base and normality in every base are not equivalent definitions.

In a 1950 note on the decimal digits of $\sqrt{2}$, Borel [Bor50] conjectured that every
irrational algebraic number is normal in every base. This was the first publication to address
the expansion of an irrational algebraic number [AB07].

For the characterisation of normality by uniform distribution modulo $1$, see
`FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean`.

*References:*
- [Wikipedia: Normal number](https://en.wikipedia.org/wiki/Normal_number)
- [Bor50] Borel, Émile. "Sur les chiffres décimaux de $\sqrt{2}$ et divers problèmes de
  probabilités en chaîne." C. R. Acad. Sci. Paris 230 (1950): 591-593.
- [AB07] Adamczewski, Boris, and Yann Bugeaud. "On the complexity of algebraic numbers I.
  Expansions in integer bases." Annals of Mathematics 165.2 (2007): 547-565.
- [BC01] Bailey, David H., and Richard E. Crandall. "On the random character of fundamental constant
  expansions." Experimental Mathematics 10.2 (2001): 175-190.
  https://projecteuclid.org/journals/experimental-mathematics/volume-10/issue-2/On-the-random-character-of-fundamental-constant-expansions/em/999188630.full
-/

section

open NormalNumber

namespace AlgebraicNormality

/-- A real number is irrational algebraic if it is algebraic over `ℚ` but not rational. -/
def IsIrrationalAlgebraic (x : ℝ) : Prop :=
  IsAlgebraic ℚ x ∧ Irrational x

end AlgebraicNormality
