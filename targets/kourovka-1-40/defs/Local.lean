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

/-! Ported mechanically from `FormalConjectures/Kourovka/1_40.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Conjecture 1.40

by Sh. S. Kemkhadze

Is a group a nilgroup if it is the product of two normal nilsubgroups?

Here a nilgroup (Engel group) is a group in which every element is an Engel
element. This is the Engel-group analogue of Fitting's theorem, which
guarantees that the product of two normal nilpotent subgroups is nilpotent.

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v40)
-/

section

open scoped commutatorElement

namespace Kourovka.«1.40»

variable {G : Type*} [Group G]

/-- The iterated commutator $[x,\, {}_n y]$, defined by $[x,\, {}_0 y] = x$ and
$[x,\, {}_{n+1} y] = [[x,\, {}_n y], y]$. -/
def engelCommutator (x y : G) : ℕ → G
  | 0 => x
  | n + 1 => ⁅engelCommutator x y n, y⁆

/-- An element $y$ of a group $G$ is a (left) Engel element if for every
$x \in G$ there is some $n$ with $[x,\, {}_n y] = 1$. -/
def IsEngelElement (y : G) : Prop :=
  ∀ x : G, ∃ n : ℕ, engelCommutator x y n = 1

/-- A nilgroup (Engel group) is a group in which every element is an Engel
element. -/
def IsEngelGroup (G : Type*) [Group G] : Prop :=
  ∀ y : G, IsEngelElement y

end Kourovka.«1.40»
