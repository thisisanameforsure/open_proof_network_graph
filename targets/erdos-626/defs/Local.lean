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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/626.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 626

*References:*
- [erdosproblems.com/626](https://www.erdosproblems.com/626)
- [Er59b] Erdős, P., *Graph theory and probability*. Canadian J. Math. (1959), 34-38.
- [Er62b] Erdős, P., *On circuits and subgraphs of chromatic graphs*. Mathematika (1962),
  170-175.
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Ko88] Kostochka, A. V., *Upper bounds on the chromatic number of graphs*. Trudy Inst. Mat.
  (Novosibirsk) (1988), 204-226, 265.
-/

section

open Filter
open scoped Topology

namespace Erdos626

/--
`g k n` is $g_k(n)$: the largest $m$ such that some graph on $n$ vertices has chromatic number
exactly $k$ and girth $> m$, that is, no cycle of length $\leq m$.

The girth is `SimpleGraph.egirth`, which is `⊤` for an acyclic graph. The value `sSup ∅ = 0`
for $n < k$ affects only finitely many $n$. For $k \leq 2$ the set is unbounded whenever an
acyclic graph on $n$ vertices with chromatic number $k$ exists, and then `sSup` is also $0$; this
case is not used below, where $k \geq 4$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ (m : ℕ∞) < G.egirth}

/--
`h m n` is $h^{(m)}(n)$: the largest chromatic number of a graph on $n$ vertices with girth
$> m$.
-/
noncomputable def h (m n : ℕ) : ℕ :=
  sSup {c : ℕ | ∃ G : SimpleGraph (Fin n), (m : ℕ∞) < G.egirth ∧ G.chromaticNumber = c}

end Erdos626
