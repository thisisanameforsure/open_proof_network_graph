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

/-! Ported mechanically from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/EdgeColouring.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the module `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.EdgeColouring`, lemmas included. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

section

/-!
# Edge colourings of a SimpleGraph

`SimpleGraph.IsEdgeColouring H c` asserts that `c : ι → SimpleGraph V` is a partition of
the edges of `H` into colour classes indexed by `ι`. The classes must (1) cover `H`
(`H = ⨆ i, c i`) and (2) be pairwise disjoint (each edge belongs to exactly one class).

This unifies the previous local `IsNEdgeColouring` (`ι = Fin n`) and `IsCountableEdgeColouring`
(`ι = ℕ`) shapes used in `FormalConjectures/ErdosProblems/596.lean`. The two are now special
cases of `IsEdgeColouring` parameterised by the index type.

`SimpleGraph.TopEdgeLabeling.CliqueFree` is the Ramsey-theoretic condition on the other
edge-colouring shape Mathlib provides, a labelling of the edges of the complete graph: no
colour class contains a clique of the given size.
-/

namespace SimpleGraph

/-- `IsEdgeColouring H c` asserts that `c : ι → SimpleGraph V` is a partition of the edges
of `H`: the colour classes cover `H` (`H = ⨆ i, c i`) and are pairwise disjoint. -/
def IsEdgeColouring {V ι : Type*} (H : SimpleGraph V) (c : ι → SimpleGraph V) : Prop :=
  H = ⨆ i, c i ∧ ∀ i j, i ≠ j → Disjoint (c i) (c j)

/-- A labelling of the edges of the complete graph on `V` by `ι` is `n`-clique-free when no
colour class contains an `n`-clique, that is, when it admits no monochromatic `n`-clique. -/
def TopEdgeLabeling.CliqueFree {V ι : Type*} (C : TopEdgeLabeling V ι) (n : ℕ) : Prop :=
  ∀ i : ι, (C.labelGraph i).CliqueFree n

end SimpleGraph
