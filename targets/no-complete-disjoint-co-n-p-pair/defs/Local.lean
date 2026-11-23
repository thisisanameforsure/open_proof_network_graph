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
import Defs.ComputabilityBitstringEncoding
import Defs.ComputabilityComplexity
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Paper/DisjointNPPairs.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Complete disjoint NP pairs

*References:*
* [Ra94] Razborov, A. A. (1994). "On provably disjoint NP-pairs." *BRICS Report Series*
  RS-94-36; ECCC TR94-006.
* [KMT03] Köbler, J., Messner, J., and Torán, J. (2003). "Optimal proof systems imply complete
  sets for promise classes." *Inform. and Comput.* 184, pp. 71--92.
* [GSSZ04] Glaßer, C., Selman, A. L., Sengupta, S., and Zhang, L. (2004). "Disjoint NP-pairs."
  *SIAM J. Comput.* 33, pp. 1369--1416.
* [Pu17] Pudlák, P. (2017). "Incompleteness in the finite domain." *Bull. Symbolic Logic* 23,
  pp. 405--441. [arXiv:1601.01487](https://arxiv.org/abs/1601.01487)
* [Kh22] Khaniki, E. (2022). "New relations and separations of conjectures about incompleteness
  in the finite domain." *J. Symbolic Logic* 87, pp. 912--937.
  [arXiv:1904.01362](https://arxiv.org/abs/1904.01362)
-/

section

namespace DisjointNPPairs

open ComplexityTheory

/-- A **disjoint NP pair**: two languages in `NP` with no common element. -/
structure IsDisjointNPPair (A B : DecisionProblem) : Prop where
  memA : A ∈ NP
  memB : B ∈ NP
  disjoint : ∀ x, ¬(A x = true ∧ B x = true)

/-- A **disjoint coNP pair**: two languages in `coNP` with no common element. -/
structure IsDisjointCoNPPair (A B : DecisionProblem) : Prop where
  memA : A ∈ coNP
  memB : B ∈ coNP
  disjoint : ∀ x, ¬(A x = true ∧ B x = true)

/-- The pair `(A, B)` **reduces** to the pair `(A', B')`: a polynomial-time map sends `A` into
`A'` and `B` into `B'` (a many-one reduction of pairs, [GSSZ04, Theorem 2.14]). -/
def PairReducible (A B A' B' : DecisionProblem) : Prop :=
  ∃ f : List Bool → List Bool, IsPolyTime f ∧
    (∀ x, A x = true → A' (f x) = true) ∧ (∀ x, B x = true → B' (f x) = true)

/-- `(A, B)` is a **complete disjoint NP pair**: a disjoint NP pair to which every disjoint NP
pair reduces. -/
def IsCompleteNPPair (A B : DecisionProblem) : Prop :=
  IsDisjointNPPair A B ∧ ∀ A' B', IsDisjointNPPair A' B' → PairReducible A' B' A B

/-- `(A, B)` is a **complete disjoint coNP pair**. -/
def IsCompleteCoNPPair (A B : DecisionProblem) : Prop :=
  IsDisjointCoNPPair A B ∧ ∀ A' B', IsDisjointCoNPPair A' B' → PairReducible A' B' A B

/-- A pair `(A, B)` is **P-separable** if some language in `P` contains `A` and misses `B`. -/
def IsPSeparable (A B : DecisionProblem) : Prop :=
  ∃ S ∈ P, (∀ x, A x = true → S x = true) ∧ ∀ x, B x = true → S x = false

end DisjointNPPairs
