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

/-! Ported mechanically from `FormalConjectures/ErdosProblems/78.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 78

*References:*
- [erdosproblems.com/78](https://www.erdosproblems.com/78)
- [Co15] Cohen, Gil, *Two-source dispersers for polylogarithmic entropy and improved Ramsey
  graphs*. arXiv:1506.04428 (2015).
- [Er47] Erdős, P., *Some remarks on the theory of graphs*. Bull. Amer. Math. Soc. (1947),
  292-294.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er88] Erdős, P, Problems and results in combinatorial analysis and graph theory. Discrete Math.
  (1988), 81-92.
- [Er93] Erdős, Paul, Some of my favorite solved and unsolved problems in graph theory. Quaestiones
  Math. (1993), 333-350.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul
  Erdős, I (1997), 47-67.
- [Li23b] Li, Xin, *Two source extractors for asymptotically optimal entropy, and (many) more*.
  arXiv:2303.06802 (2023).
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
-/

section

open Filter Real ComplexityTheory

namespace Erdos78

/--
The graph on `Fin n` described by an adjacency oracle `adj`. Two distinct vertices `u` and `v`
are adjacent if `adj (1ⁿ, u, v)` or `adj (1ⁿ, v, u)` is `true`.

The number of vertices is given in unary, as the list `List.replicate n true`. So if `adj` is
computable in polynomial time, then the whole graph on `n` vertices is computable in time
polynomial in `n`. This is the notion of a *weakly explicit* family of graphs; compare
`stronglyExplicitGraph`.
-/
def explicitGraph (adj : List Bool × ℕ × ℕ → Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v ↦ adj (List.replicate n true, u, v)

/--
The graph on `Fin n` described by an adjacency oracle `adj` which receives `n` in binary. Two
distinct vertices `u` and `v` are adjacent if `adj (n, u, v)` or `adj (n, v, u)` is `true`.

If `adj` is computable in polynomial time, then each adjacency query is answered in time
polynomial in $\log n$. This is the notion of a *strongly explicit* family of graphs, which is
what "explicit Ramsey graph" usually means in the literature (e.g. [Co15], [Li23b]). Compare
`explicitGraph`, where only time polynomial in $n$ is allowed.
-/
def stronglyExplicitGraph (adj : ℕ × ℕ × ℕ → Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v ↦ adj (n, u, v)

/--
The graph `G` has no clique and no independent set with `m` vertices.
-/
def NoHomogeneousSet {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree m

end Erdos78
