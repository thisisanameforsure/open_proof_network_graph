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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/467.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 467

*Reference:* [erdosproblems.com/467](https://www.erdosproblems.com/467)
-/

section

namespace Erdos467

open Filter

/-- The finite set of primes at most $x$. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.Icc 2 x).filter Nat.Prime

/-- The sets $A$ and $B$ form a disjoint nonempty decomposition of the primes up to $x$. -/
def PrimePartitionUpTo (x : ℕ) (A B : Finset ℕ) : Prop :=
  A.Nonempty ∧
    B.Nonempty ∧
      A ∪ B = primesUpTo x ∧
        A ∩ B = ∅

/--
The selected congruence classes cover every $n<x$ from both sides of the partition.
-/
def CongruenceCover (x : ℕ) (residue : ℕ → ℕ) (A B : Finset ℕ) : Prop :=
  ∀ n : ℕ,
    n < x →
      (∃ p : ℕ, p ∈ A ∧ n % p = residue p % p) ∧
        ∃ q : ℕ, q ∈ B ∧ n % q = residue q % q

end Erdos467
