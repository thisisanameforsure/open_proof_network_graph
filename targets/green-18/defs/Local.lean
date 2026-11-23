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
import Defs.ComputabilityTuringMachineBusyBeavers
import Defs.ComputabilityTuringMachineNotation
import Defs.ComputabilityTuringMachinePostTuringMachine
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/GreensOpenProblems/18.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Ben Green's Open Problem 18

*Reference:*
- [Gr26] [Ben Green's Open Problem 18](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.18)
- [Au16] Austin, Tim. "Ajtai–Szemerédi theorems over quasirandom groups." Recent trends in
  combinatorics. Cham: Springer International Publishing, 2016. 453-484.
- [So13] Solymosi, Jozsef. "Roth-type theorems in finite groups." European Journal of Combinatorics
  34.8 (2013): 1454-1458.
- [Go01] Gowers, William T. "A new proof of Szemerédi's theorem." Geometric & Functional Analysis
  GAFA 11.3 (2001): 465-588.
-/

section

open Finset

namespace Green18

/--
The number of triples $(x, y, g)$ in $G^3$ such that $g \neq e$, and $(x, y), (gx, y), (x, gy)$ are
all in $A$. These are called "naive corners" by [Au16].

Note: the shortened formulation from [Gr26] does not mention $g \neq e$, but this is the original
statement from [Au16], which ensure non-trivial corners. Note however that [Au16] use more
generally compact groups and not just finite discrete groups.
-/
def numNaiveCorners {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)) : ℕ :=
  ( (univ : Finset (G × G × G)).filter
    fun ⟨x, y, g⟩ => g ≠ 1 ∧ (x, y) ∈ A ∧ (g * x, y) ∈ A ∧ (x, g * y) ∈ A
  ).card

/--
The number of triples $(x, y, g)$ in $G^3$ such that $g \neq e$, and $(x, y), (xg, y), (x, gy)$ are
all in $A$. These are called "BMZ corners" by [Au16].
-/
def numBmzCorners {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)) : ℕ :=
  (
    (univ : Finset (G × G × G)).filter
    fun ⟨x, y, g⟩ => g ≠ 1 ∧ (x, y) ∈ A ∧ (x * g, y) ∈ A ∧ (x, g * y) ∈ A
  ).card

end Green18
