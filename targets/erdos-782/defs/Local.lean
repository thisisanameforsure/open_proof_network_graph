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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/782.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 782

*References:*
- [erdosproblems.com/782](https://www.erdosproblems.com/782)
- [BEF90] Brown, T. C. and Erdős, P. and Freedman, A. R., _Quasi-progressions and descending
  waves_. J. Combin. Theory Ser. A 53 (1990), 81-95.
- [BFS03] Brown, T. C., Freedman, A. R. and Shiue, P. J.-S., _Progressions of squares_.
  Australas. J. Combin. 27 (2003), 187-192.
- [BEU26] Bremner, A., Elsholtz, C. and Ulas, M., _There are infinitely many Hilbert cubes of
  dimension 3 in the set of squares_. [arXiv:2604.05459](https://arxiv.org/abs/2604.05459) (2026).
- [CiGr07] Cilleruelo, J. and Granville, A., _Lattice points on circles, squares in arithmetic
  progressions and sumsets of squares_. Additive combinatorics (2007), 241-262.
- [DiEl12] Dietmann, R. and Elsholtz, C., _Hilbert cubes in progression-free sets and in the set
  of squares II_. [arXiv:1207.1461](https://arxiv.org/abs/1207.1461) (2012).
- [So07] Solymosi, J., _Elementary additive combinatorics_. Additive combinatorics (2007), 29-38.
-/

section

namespace Erdos782

/-- `ContainsQuasiProgression S C k` says that `S` contains a $k$-term quasi-progression of
diameter $C$: terms $x_1,\ldots,x_k\in S$ and a difference $d\geq 1$ with
$x_i+d\leq x_{i+1}\leq x_i+d+C$ for all $1\leq i<k$ (indexed from $0$ in Lean). The condition
$d\geq 1$ makes the terms strictly increasing, as in [BFS03]. -/
def ContainsQuasiProgression (S : Set ℕ) (C k : ℕ) : Prop :=
  ∃ (x : ℕ → ℕ) (d : ℕ), 0 < d ∧ (∀ i < k, x i ∈ S) ∧
    ∀ i, i + 1 < k → x i + d ≤ x (i + 1) ∧ x (i + 1) ≤ x i + d + C

/-- The Hilbert cube with presentation $(a_0; b_1,\ldots,b_d)$, that is,
$$a_0+\left\{ \sum_i \epsilon_ib_i : \epsilon_i\in \{0,1\}\right\}.$$
The index set of the sum is the set of $i$ with $\epsilon_i=1$. -/
def hilbertCube {d : ℕ} (a₀ : ℤ) (b : Fin d → ℤ) : Set ℤ :=
  {x | ∃ ε : Finset (Fin d), x = a₀ + ∑ i ∈ ε, b i}

end Erdos782
