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
import Defs.AlgebraOrderGroupPointwiseInterval
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataSetDensity
import Defs.DataSetInterval
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.OrderIntervalFinsetBasic
import Defs.OrderIntervalFinsetNat

/-! Ported mechanically from `FormalConjectures/ErdosProblems/408.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 408

*References:*
- [erdosproblems.com/408](https://www.erdosproblems.com/408)
- [OEIS A003434](https://oeis.org/A003434): the values $f(n)$ for $n \geq 2$.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980).
- [Pi29] Pillai, S. Sivasankaranarayana, *On a function connected with $\phi(n)$*. Bull. Amer.
  Math. Soc. 35 (1929), 837-841.
  [doi:10.1090/S0002-9904-1929-04800-6](https://doi.org/10.1090/S0002-9904-1929-04800-6)
- [Sh50] Shapiro, Harold N., *On the iterates of a certain class of arithmetic functions*. Comm.
  Pure Appl. Math. 3 (1950), 259-272.
- [EGPS90] Erdős, P., Granville, A., Pomerance, C. and Spiro, C., *On the normal behavior of the
  iterates of some arithmetic functions*. Analytic number theory (Allerton Park, IL, 1989),
  Progr. Math. 85 (1990), 165-204.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. Third edition, Springer (2004),
  Problem B41.
- [FKL10] Ford, K., Konyagin, S. V. and Luca, F., *Prime chains and Pratt trees*. Geom. Funct.
  Anal. 20 (2010), 1231-1258. [arXiv:0904.0473](https://arxiv.org/abs/0904.0473)
  [doi:10.1007/s00039-010-0089-0](https://doi.org/10.1007/s00039-010-0089-0)
-/

section

open Filter
open scoped Topology

namespace Erdos408

/--
`f n` is $f(n) = \min\{k \geq 1 : \phi_k(n) = 1\}$, where $\phi_1 = \phi$ is Euler's totient
function and $\phi_k(n) = \phi(\phi_{k-1}(n))$. As in the source, $k$ starts at $1$, so
$f(1) = 1$. Every iterate of $\phi$ at $0$ is $0$, so `sInf ∅ = 0` gives the junk value
$f(0) = 0$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ Nat.totient^[k] n = 1}

end Erdos408
