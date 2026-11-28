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

/-! Ported mechanically from `FormalConjecturesForMathlib/Topology/LebesgueCoveringDimension.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the module `FormalConjecturesForMathlib.Topology.LebesgueCoveringDimension`, lemmas included. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

section

/--
A topological space `X` has Lebesgue covering dimension at most `n` if every finite
open cover of `X` admits a finite open refinement in which no point of `X` is contained
in more than `n + 1` elements.
-/
def HasLebesgueCoveringDimensionLE (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (𝓤 : Set (Set X)), 𝓤.Finite → (∀ U ∈ 𝓤, IsOpen U) → ⋃₀ 𝓤 = Set.univ → ∃ 𝓥 : Set (Set X), 𝓥.Finite ∧ (∀ V ∈ 𝓥, IsOpen V) ∧ ⋃₀ 𝓥 = Set.univ ∧
  (∀ V ∈ 𝓥, ∃ U ∈ 𝓤, V ⊆ U) ∧ ∀ x : X, {V ∈ 𝓥 | x ∈ V}.encard ≤ (n + 1 : ℕ)

/--
A topological space `X` has Lebesgue covering dimension exactly `n` if it has covering
dimension at most `n` but not at most `n - 1`.
-/
def HasLebesgueCoveringDimensionEq (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  HasLebesgueCoveringDimensionLE X n ∧ ∀ m, m < n → ¬ HasLebesgueCoveringDimensionLE X m
