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
import Defs.CombinatoricsAdditiveRestrictedSumset
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/2.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Ben Green's Open Problem 2

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.2)
- [Er65] P. Erdős. Extremal problems in number theory, In Proc. Sympos. Pure Math., Vol. VIII,
  pages 181–189. Amer. Math. Soc., Providence, R.I., 1965.
- [Sa21] Sanders, Tom. "The Erdős–Moser Sum-free Set Problem." Canadian Journal of Mathematics 73.1
  (2021): 63-107.
- [Ru05] I. Z. Ruzsa, Sum-avoiding subsets. Ramanujan J., 9 (2005) (1-2):77–82.
- [Ch71] S. L. G. Choi. On a combinatorial problem in number theory. Proc. London Math. Soc. (3),
  23:629–642, 1971. doi:10.1112/plms/s3-23.4.629.
- [BSS00] A. Baltz, T. Schoen, and A. Srivastav. Probabilistic construction of small strongly
  sum-free sets via large Sidon sets. Colloq. Math., 86(2):171–176, 2000.
  doi:10.4064/cm-86-2-171-176.
-/

section

open Filter
open scoped Topology

namespace Green2

/--
We define the construction from [Sa21, p1] as
$M(A) := \max \{|S| : S \subseteq A \text{ and } (S \hat{+} S) \cap A = \varnothing \}$.
-/
def maxRestrictedSumAvoidingSubsetSize (A : Finset ℤ) : ℕ :=
  (A.powerset.filter fun S => Disjoint S.restrictedSumset A).sup Finset.card

/-
TODO(jeangud): Add additional bounds on non-negative integers from Selfridge [Er65, p187], and
Choi [Er65, p190], and [BSS00].
-/

end Green2
