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
import Defs.CombinatoricsAPBasic
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryAbsoluteGaloisGroup
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Wikipedia/Taxicab.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Taxicab numbers

A *taxicab number* for natural numbers $k, m, n$ is the
smallest number $x$ that can be expressed as a sum of $m$
positive $k$-th powers in at least $n$ distinct ways. The
most famous taxicab number is
$ 1729 = 1³ + 12³ = 9³ + 10³, $
also known as the Hardy–Ramanujan number.

However, a taxicab number is not known for $k=5$, $m=2$, and any $n ≥ 2$:
No positive integer is known that can be written as the
sum of two 5th powers in more than one way, and it is not
known whether such a number exists.

In particular, it is not known whether there exists a
taxicab number for $k=5$, $m=2$, and $n=2$.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Taxicab_number)
 - [Generalized taxicab number](https://en.wikipedia.org/wiki/Generalized_taxicab_number)
 - [OEIS taxicab cubes](https://oeis.org/A001235)
 - [OEIS taxicab 4th powers](https://oeis.org/A018786)
 - [OEIS taxicab conjecture](https://oeis.org/A088703)
-/

section

namespace Taxicab

/-- $x$ is a candidate for being a taxicab number for $k, m, n$ if there exist at least $n$
distinct multisets of $m$ positive integers such that the sum of the $k$-th powers of the
elements of each multiset is $x$. Using multisets means that two representations that
differ only in the order of their terms count as one way.
-/
def IsTaxicabFor' (k m n x : ℕ) : Prop :=
  ∃ S : Finset (Multiset ℕ), n ≤ S.card ∧
    ∀ L ∈ S, Multiset.card L = m ∧ 0 ∉ L ∧ (L.map (· ^ k)).sum = x

/-- $x$ is a taxicab number if it is the smallest number
that can be expressed as a sum of $m$ positive $k$-th
powers in at least $n$ distinct ways.
-/
def IsTaxicabFor (k m n : ℕ) (x : ℕ) : Prop :=
  IsLeast { x : ℕ | IsTaxicabFor' k m n x } x

end Taxicab
