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
import Defs.CombinatoricsStableMarriage
import Defs.CombinatoricsStableMarriageUnbalanced
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Arxiv/2406.10319/StableMatchingHyperbola.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Pittel's stable-matching hyperbola threshold conjecture

*Reference:*
[On Constrained Matchings, Stable Under Random Preferences](https://doi.org/10.1002/rsa.70036)
by Boris Pittel, Section 6, Notes (2).
The conjecture also appears in the [arXiv preprint, p. 26](https://arxiv.org/pdf/2406.10319#page=26).
-/

section

open Filter MeasureTheory StableMarriage
open scoped Topology

namespace Arxiv.«2406.10319»

/-- The joint law of the uniform preference profile and the independent admissibility mask. -/
noncomputable def marketLaw (n : ℕ) (p : unitInterval) : Measure (Profile n × Admissibility n) :=
  (uniformProfile n).toMeasure.prod (Admissibility.law n p)

/-- The rank products are within $\varepsilon$ of $1$ after scaling both ranks by $\sqrt{pn^3}$,
and the scaled pairs cover the arc $(t,t^{-1})$ for $t \in [2/3,3/2]$ to that tolerance in each
coordinate. The event is empty when $n=0$ or $p=0$, where the scale vanishes. -/
def hyperbolaEvent (n : ℕ) (p : unitInterval) (ε : ℝ) : Set (Profile n × Admissibility n) :=
  {ω |
    let s := Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3)
    let q (M : PartialMatching n) := (totalWifeRank ω.1 ω.2 M : ℝ) / s
    let r (M : PartialMatching n) := (totalHusbandRank ω.1 ω.2 M : ℝ) / s
    0 < n ∧ 0 < (p : ℝ) ∧
      (∀ M, IsPartialStable ω.1 ω.2 M → |q M * r M - 1| ≤ ε) ∧
      ∀ t ∈ Set.Icc (2 / 3 : ℝ) (3 / 2), ∃ M, IsPartialStable ω.1 ω.2 M ∧
        max |q M - t| |r M - t⁻¹| ≤ ε}

end Arxiv.«2406.10319»
