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
import Defs.DataNatPrimeComposite

/-! Ported mechanically from `FormalConjecturesForMathlib/NumberTheory/SierpinskiNumber.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the module `FormalConjecturesForMathlib.NumberTheory.SierpinskiNumber`, lemmas included. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

section

/-!
# Sierpiński numbers

*References:*
- [Wikipedia, Sierpiński number](https://en.wikipedia.org/wiki/Sierpi%C5%84ski_number)
- [Si60] Sierpiński, W., Elementary Theory of Numbers. Państwowe Wydawnictwo Naukowe,
  Warsaw (1960).

A positive odd integer $k$ is a *Sierpiński number* if $k \cdot 2^n + 1$ is composite for all
natural numbers $n$.
-/

namespace Nat

/--
A positive odd integer $k$ is a
[Sierpiński number](https://en.wikipedia.org/wiki/Sierpi%C5%84ski_number) if $k \cdot 2^n + 1$
is composite for all natural numbers $n$. In other words, every member of the set
$\{k \cdot 2^n + 1 : n \in \mathbb{N}\}$ is composite.
-/
def IsSierpinskiNumber (k : ℕ) : Prop :=
  ¬ 2 ∣ k ∧ ∀ n, (k * 2 ^ n + 1).Composite

end Nat
