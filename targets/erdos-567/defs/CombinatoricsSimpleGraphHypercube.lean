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

/-! Ported mechanically from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Hypercube.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the module `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Hypercube`, lemmas included. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

section

/-!
# The hypercube graph

`SimpleGraph.hypercube n` is the graph `Qₙ` on the `n`-bit vectors, with two vectors adjacent when
they differ in exactly one coordinate. It has `2 ^ n` vertices and `n * 2 ^ (n - 1)` edges.
-/

namespace SimpleGraph

open scoped Finset

/-- `hypercube n` is the `n`-dimensional hypercube graph `Qₙ`: the vertices are the `n`-bit
vectors, and two vertices are adjacent when they differ in exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := #{i | u i ≠ v i} = 1
  symm.symm _ _ := by simp [eq_comm]
  loopless.irrefl _ := by simp

instance (n : ℕ) : DecidableRel (hypercube n).Adj :=
  fun u v ↦ inferInstanceAs (Decidable (#{i | u i ≠ v i} = 1))

@[simp]
theorem hypercube_adj {n : ℕ} {u v : Fin n → Bool} :
    (hypercube n).Adj u v ↔ #{i | u i ≠ v i} = 1 := Iff.rfl

end SimpleGraph
