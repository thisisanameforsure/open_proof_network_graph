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
import Defs.NumberTheoryPrimeGap

/-! Ported mechanically from `FormalConjectures/ErdosProblems/5.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 5

*References:*
- [erdosproblems.com/5](https://www.erdosproblems.com/5)
- [BFM16] Banks, William D. and Freiberg, Tristan and Maynard, James, *On limit points of the
  sequence of normalized prime gaps*. Proc. Lond. Math. Soc. (3) (2016), 515-539.
- [Er55] Erdős, Paul, *Some remarks on number theory*. Riveon Lematematika (1955), 45-48.
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [Er85c] Erdős, P., *On some of my problems in number theory I would most like to see solved*.
  Number theory (Ootacamund, 1984) (1985), 74-84.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős,
  I (1997), 47-67.
- [GPY09] Goldston, Daniel A. and Pintz, János and Yıldırım, Cem Y., *Primes in tuples. I*.
  Ann. of Math. (2) (2009), 819-862.
- [HiMa88] Hildebrand, Adolf and Maier, Helmut, *Gaps between prime numbers*. Proc. Amer. Math.
  Soc. (1988), 1-9.
- [Me20] Merikoski, Jori, *Limit points of normalized prime gaps*. J. Lond. Math. Soc. (2) (2020),
  99-124.
- [Pi16] Pintz, János, *Polignac numbers, conjectures of Erdős on gaps between primes, arithmetic
  progressions in primes, and the bounded gap conjecture*. From arithmetic to zeta-functions
  (2016), 367-384.
- [Ri56] Ricci, Giovanni, *Recherches sur l'allure de la suite $\{p_{n+1}-p_n/\log p_n\}$*.
  Colloque sur la Théorie des Nombres, Bruxelles, 1955 (1956), 93-106.
- [We31] Westzynthius, E., *Über die Verteilung der Zahlen, die zu den n ersten Primzahlen
  teilerfremd sind*. Commentat. Phys. Math. (1931), 1-37.
-/

section

open Filter MeasureTheory Real Set
open scoped Topology

namespace Erdos5

/--
The normalised prime gap $\frac{p_{n+1}-p_n}{\log n}$, where $p_n$ denotes the $n$-th prime.
-/
noncomputable def normalizedGap (n : ℕ) : ℝ := primeGap n / log n

/--
The set $S$ of limit points of $\frac{p_{n+1}-p_n}{\log n}$.

Only the *finite* limit points are collected here; that $\infty$ is also a limit point is
Westzynthius' theorem, recorded separately as `erdos_5.variants.westzynthius`.

Erdős' question, as well as [HiMa88] and [Pi16], normalises the prime gaps by $\log n$, whereas
[GPY09], [BFM16] and [Me20] normalise by $\log p_n$. Since $\log p_n/\log n \to 1$ the two
normalisations have the same limit points, so all the results below are stated for the
normalisation used here.
-/
def limitPointSet : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGap}

-- See also Erdős Problem 234, which concerns the density of the integers `n` with
-- `(p (n + 1) - p n) / log n < c`.

end Erdos5
