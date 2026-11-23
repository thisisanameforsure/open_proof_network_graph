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
import Defs.DataNatPrimeComposite

/-! Ported mechanically from `FormalConjectures/ErdosProblems/1059.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 1059

*Reference:* [erdosproblems.com/1059](https://www.erdosproblems.com/1059)
-/

section

namespace Erdos1059

def IsFactorial (d : ℕ) : Prop :=
  d ∈ Set.range Nat.factorial

def factorialsLessThanN (n : ℕ) : Set ℕ :=
  { d | d < n ∧ IsFactorial d }

def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀d ∈ factorialsLessThanN n, (n - d).Composite

abbrev DecidableIsFactorial (d : ℕ) : Prop :=
  ((Finset.Icc 0 d).filter (λ k => Nat.factorial k = d)).Nonempty

def decidableFactorialsLessThanN (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter DecidableIsFactorial

def DecidableAllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ d ∈ decidableFactorialsLessThanN n, (n - d).Composite

end Erdos1059
