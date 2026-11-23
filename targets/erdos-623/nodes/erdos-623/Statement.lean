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

/-! Erdős problem 623: Let $X$ be a set of cardinality $\aleph_\omega$ and $f$ be a function from the finite subsets of $X$ to $X$ such that $f(A)\not\in A$ for all $A$. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/623.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter Real Set
open scoped Cardinal Ordinal

theorem Opn.erdos_623 :
    ∀ (X : Type u) (hX : #X = ℵ_ ω)
    (f : Finset X → X), (∀ A : Finset X, f A ∉ A) →
    (∃ Y : Set X, Set.Infinite Y ∧ (∀ (B : Finset X), ↑B ⊆ Y → f B ∉ Y)) := by
  sorry
