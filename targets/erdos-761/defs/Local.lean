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
import Defs.CombinatoricsDigraphTournament
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/761.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 761

*References:*
- [erdosproblems.com/761](https://www.erdosproblems.com/761)
- [ErGi93] Erdős, P. and Gimbel, J., *Some problems and results in cochromatic theory*.
  Quo vadis, graph theory? (1993), 261-264.
-/

section

universe u

namespace Erdos761

/-- The vertices in `S` span no directed cycle of `D`: there is no closed directed walk of
positive length inside `S`. -/
def IsAcyclicOn {V : Type*} (D : Digraph V) (S : Set V) : Prop :=
  ∀ v : V, ¬ Relation.TransGen (fun a b : V ↦ a ∈ S ∧ b ∈ S ∧ D.Adj a b) v v

/-- `Dicolorable G k` says that, for every orientation `D` of `G`, the vertices can be coloured
with `k` colours such that no colour class contains a directed cycle of `D`. -/
def Dicolorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ D : Digraph V, D.IsOrientation G →
    ∃ c : V → Fin k, ∀ i : Fin k, IsAcyclicOn D {v | c v = i}

/-- The dichromatic number $\delta(G)$: the least `k` such that `G` is `k`-dicolorable. It is
finite for finite graphs, since colouring all vertices differently works. -/
noncomputable def dichromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : Dicolorable G k), (k : ℕ∞)

end Erdos761
