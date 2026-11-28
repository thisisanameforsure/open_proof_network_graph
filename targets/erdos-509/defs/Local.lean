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
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.ComputabilityTuringMachineBusyBeavers
import Defs.ComputabilityTuringMachinePostTuringMachine
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/509.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 509

*Reference:* [erdosproblems.com/509](https://www.erdosproblems.com/509)
-/

section

namespace Erdos509

open Polynomial
open scoped Real

section BoundedDiscCover

universe u v

variable {M : Type u} [MetricSpace M]

/-- An $r$-bounded disc cover of a subset of a metric space $M$
is an indexed family of closed discs whose radii sum to at most $r$. -/
structure BoundedDiscCover (S : Set M) (r : ℝ) (ι : Type v) where
  (C : ι → M)
  (R : ι → ℝ)
  (h_cover : S ⊆ ⋃ (i : ι), Metric.closedBall (C i) (R i))
  (h_summable : Summable (fun i : ι => R i))
  (h_bdd : ∑' i, R i ≤ r)
  (h_pos : ∀ i, 0 < R i)

variable (S : Set M) (r : ℝ)

noncomputable def boundedDiscCover_empty [Nonempty M] (r : ℝ) (hr : 0 < r) :
  (BoundedDiscCover (∅ : Set M) r (PUnit : Type v)) where
  C := fun _ => Classical.ofNonempty
  R := fun _ => r
  h_cover := Set.empty_subset _
  h_summable := (hasSum_fintype _).summable
  h_bdd := by
    have := hasSum_fintype fun (_ : (PUnit : Type v)) => if 0 ≤ r then -1 else r
    simp only [tsum_const, Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton, one_smul,
      ge_iff_le]
    bound
  h_pos := by aesop

end BoundedDiscCover

end Erdos509
