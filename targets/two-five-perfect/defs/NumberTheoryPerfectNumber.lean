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

/-! Ported mechanically from `FormalConjecturesForMathlib/NumberTheory/PerfectNumber.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the module `FormalConjecturesForMathlib.NumberTheory.PerfectNumber`, lemmas included. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Iterated perfect numbers

A positive integer is $(m,k)$-perfect if the $m$-fold iterate of the sum-of-divisors
function equals $k$ times that integer.
-/

section

open scoped ArithmeticFunction.sigma

namespace Nat

/--
A positive integer $n$ is $(m,k)$-perfect if $\sigma^m(n) = kn$, where $\sigma^m$ is
the $m$-th iterate of the sum-of-divisors function $\sigma$.
-/
def IsPerfectFor (n m k : ℕ) : Prop :=
  0 < n ∧ Nat.iterate (fun x => σ 1 x) m n = k * n

/-- Zero is excluded from the definition of an iterated perfect number. -/
@[simp]
theorem not_isPerfectFor_zero (m k : ℕ) : ¬ IsPerfectFor 0 m k := by
  simp [IsPerfectFor]

end Nat
