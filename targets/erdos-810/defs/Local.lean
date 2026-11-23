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
import Defs.AnalysisSpecialFunctionsAdditiveCharacter

/-! Ported mechanically from `FormalConjectures/ErdosProblems/810.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 810

*References:*
- [erdosproblems.com/810](https://www.erdosproblems.com/810)
- [BEGS89] Burr, S. A., Erdős, P., Graham, R. L., and Sós, V. T.,
  *Maximal anti-Ramsey graphs and the strong chromatic number*.
  J. Graph Theory 13 (1989), no. 3, 263–282.
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (1991), 397–406.
-/

section

namespace Erdos810

open Filter

/-- Four objects are pairwise distinct. -/
def PairwiseDistinct4 {α : Type _} (a b c d : α) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- The vertices $a,b,c,d$ form a $C_4$ in cyclic order. -/
def IsC4 {n : ℕ} (G : SimpleGraph (Fin n)) (a b c d : Fin n) : Prop :=
  PairwiseDistinct4 a b c d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- An edge-colouring by $n$ colours such that reversing an edge gives the same colour and every
$C_4$ receives four distinct colours. -/
def C4RainbowColoring {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Fin n → Fin n) : Prop :=
  (∀ a b, G.Adj a b → color a b = color b a) ∧
    ∀ a b c d, IsC4 G a b c d →
      PairwiseDistinct4 (color a b) (color b c) (color c d) (color d a)

end Erdos810
