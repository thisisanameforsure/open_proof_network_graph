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
import Defs.AnalysisSpecialFunctionsAdditiveCharacter

/-! Ported mechanically from `FormalConjectures/ErdosProblems/820.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 820

*References:*
- [erdosproblems.com/820](https://www.erdosproblems.com/820)
- [Er74b] Erdős, P., *Remarks on some problems in number theory*. Math. Balkanica (1974),
  197-202.
- [OEIS A263647](https://oeis.org/A263647): the $n$ with $(2^n-1, 3^n-1) = 1$.
-/

section

open Filter

namespace Erdos820

/-- $H(n)$ is the smallest integer $l$ such that there is some $k < l$ with
$(k^n-1, l^n-1) = 1$.

We take $k$ and $l$ to be integers with $k \geq 2$, so that $k^n - 1 \geq 1$ for $n \geq 1$.
Smaller $k$ give degenerate values: over the integers $k = 0$ gives $(-1, l^n-1) = 1$, and $k = 1$
gives $(0, l^n-1) = l^n-1$, which is $1$ for $n = 1$, $l = 2$. Both would contradict the value
$H(1) = 3$ listed in the source.

For $n \geq 1$ the set is nonempty (see `Erdos820.H_spec`). For $n = 0$ it is empty, and
`H 0 = 0` by the `sInf ∅` convention; the only statement whose truth depends on `H 0` is
`Erdos820.H_eq_three_iff`, where both sides are false. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf {l : ℕ | ∃ k : ℕ, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)}

/-- $K(n)$ is the smallest integer $k \geq 2$ such that $(k^n-1, 2^n-1) = 1$. As for
`Erdos820.H`, smaller $k$ are excluded because they give degenerate values.

For $n \geq 2$ the value $k = 2$ never works, and $k = 2^n - 1$ always works. For $n = 1$ we
get $K(1) = 2$, and for $n = 0$ the set is empty, so `K 0 = 0`. -/
noncomputable def K (n : ℕ) : ℕ :=
  sInf {k : ℕ | 2 ≤ k ∧ Nat.Coprime (k ^ n - 1) (2 ^ n - 1)}

end Erdos820
