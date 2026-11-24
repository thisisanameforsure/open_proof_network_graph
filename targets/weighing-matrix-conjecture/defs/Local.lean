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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Wikipedia/WeighingMatrix.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Weighing matrices and the Geramita–Seberry conjecture

A *weighing matrix* $W(n, w)$ of order $n$ and weight $w$ is an $n \times n$ matrix with entries in
$\{-1, 0, 1\}$ satisfying $W W^{\mathsf{T}} = w I_n$. At $w = n$, this recovers Hadamard matrices.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Weighing_matrix)
- [Ea76] Eades, P. (1976). *Some asymptotic existence results for orthogonal designs*, Ars Combin.
  1, 109--118.
- [GS79] Geramita, A. V. and Seberry, J. (1979). *Orthogonal Designs: Quadratic Forms and Hadamard
  Matrices*, Lecture Notes in Pure and Applied Mathematics 45, Marcel Dekker, New York.
-/

section

namespace WeighingMatrix

/-- `W` is a **weighing matrix** $W(n, w)$ of order $n$ and weight $w$ if its entries lie in
$\{-1, 0, 1\}$ and $W W^{\mathsf{T}} = w I_n$.

At $n = 0$, `Matrix (Fin 0) (Fin 0) ℤ` is a subsingleton, so the empty matrix trivially satisfies
`IsWeighingMatrix (n := 0) w 0` for every $w$; existence statements below restrict to $n \ge 1$. -/
def IsWeighingMatrix {n : ℕ} (w : ℕ) (W : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, W i j = -1 ∨ W i j = 0 ∨ W i j = 1) ∧
    W * W.transpose = (w : ℤ) • 1

end WeighingMatrix
