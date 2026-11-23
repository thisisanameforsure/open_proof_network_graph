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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/962.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 962

*References:*
- [erdosproblems.com/962](https://www.erdosproblems.com/962)
- [Er65] Erdős, P., Extremal problems in number theory. Proc. Sympos. Pure Math., Vol. VIII (1965), 181-189.
- [Er76e] Erdős, P., Problems and results on consecutive integers. Publ. Math. Debrecen (1976), 271-282.
- [Tang](https://github.com/QuanyuTang/erdos-problem-962/blob/main/On_Erd%C5%91s_Problem_962.pdf)
- [Tao](https://www.erdosproblems.com/forum/thread/962)
-/

section

open Filter Real

namespace Erdos962

/--
`Erdos962Prop n k` : there exists $m \le n$ such that each of
$m+1, \ldots, m+k$ has a prime divisor strictly larger than $k$.
-/
def Erdos962Prop (n k : ℕ) : Prop :=
  ∃ m ≤ n, ∀ i ∈ Set.Icc 1 k,
    ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ p ∣ (m + i)

/--
Let $k(n)$ be the maximal $k$ such that there exists $m \le n$ with
$m+1, \ldots, m+k$ each divisible by a prime $> k$.
-/
noncomputable def k (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun k => Erdos962Prop n k) n

end Erdos962
