/-
Copyright 2025 The Formal Conjectures Authors.

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
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex

/-! Ported mechanically from `FormalConjectures/ErdosProblems/143.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 143

*Reference:* [erdosproblems.com/143](https://www.erdosproblems.com/143)
-/

section

open Filter Finset
open scoped Topology

namespace Erdos143

/--
Let $A \subseteq (1, \infty)$ be a countably infinite set such that for all $x\neq y\in A$ and
integers $k \geq 1$ we have $|kx - y| \geq 1$.
-/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ (Set.Ioi (1 : ℝ))) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |k * x - y|))

-- TODO(firsching): add the two other conjectures.
/-
$$
\sum_{\substack{x < n \\ x \in A}} \frac{1}{x} = o(\log n)?
$$

Perhaps even

$$
\sum_{\substack{x < n \\ x \in A}} \frac{1}{x} \ll \frac{\log x}{\sqrt{\log \log x}}?
$$
-/

end Erdos143
