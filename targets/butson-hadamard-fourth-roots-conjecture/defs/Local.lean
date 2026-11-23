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
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.ComputabilityTuringMachineBusyBeavers
import Defs.ComputabilityTuringMachineNotation
import Defs.ComputabilityTuringMachinePostTuringMachine
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Butson-type Hadamard matrices

A *Butson-type Hadamard matrix* $H(k, n)$ (also written $\operatorname{BH}(n, k)$) is an
$n \times n$ complex matrix $M$ whose entries are $k$-th roots of unity ($k > 0$, $M_{ij}^k = 1$)
and whose rows are mutually orthogonal in $\mathbb{C}^n$, so that $M M^* = n I_n$. At $k = 2$,
$H(2, n)$ recovers real Hadamard matrices; at $k = 4$, $H(4, n)$ consists of matrices with entries
in $\{\pm 1, \pm i\}$.

While the Wikipedia article states as a conjecture that $H(p, m p)$ exists for every odd prime
$p \ge 3$ and integer $m \ge 1$, this fails already at $H(3, 15)$ [dL84, Wi00]. For fourth roots of
unity ($k = 4$), the complex Hadamard conjecture [Tu70, dLF11] asks whether $H(4, 2m)$ exists for
every $m \ge 1$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Butson-type_Hadamard_matrix)
- [Bu62] Butson, A. T. (1962). *Generalized Hadamard matrices*, Proc. Amer. Math. Soc. 13,
  894--898.
- [Tu70] Turyn, R. J. (1970). *Complex Hadamard matrices*, in Combinatorial Structures and their
  Applications (Calgary, 1969), Gordon and Breach, New York, 435--437.
- [dL84] de Launey, W. (1984). *On the non-existence of generalised Hadamard matrices*, J. Statist.
  Plann. Inference 10 (3), 385--396.
- [Wi00] Winterhof, A. (2000). *On the non-existence of generalized Hadamard matrices*, J. Statist.
  Plann. Inference 84, 337--342.
- [dLF11] de Launey, W. and Flannery, D. L. (2011). *Algebraic Design Theory*, Mathematical Surveys
  and Monographs 175, Amer. Math. Soc.
-/

section

namespace ButsonHadamardMatrix

/-- `M` is a **Butson-type Hadamard matrix** $H(k, n)$ if $k > 0$, every entry satisfies
$z^k = 1$, and $M M^* = n I_n$. -/
def IsButsonHadamard {n : ℕ} (k : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 < k ∧ (∀ i j, M i j ^ k = 1) ∧ M * M.conjTranspose = (n : ℂ) • 1

end ButsonHadamardMatrix
