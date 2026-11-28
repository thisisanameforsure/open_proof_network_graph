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
import Defs.CombinatoricsAPBasic
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/ErdosProblems/535.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Erdős Problem 535

*References:*
- [erdosproblems.com/535](https://www.erdosproblems.com/535)
- [Er64] P. Erdős, _On a problem in elementary number theory and a combinatorial problem_. Math.
  Comp. (1964), 644–646.
- [AbHa70] H. L. Abbott and D. Hanson, _An extremal problem in number theory_. Bull. London Math.
  Soc. (1970), 324–326.
- [Er73] P. Erdős, _Problems and results on combinatorial number theory_, in
  *A Survey of Combinatorial Theory*, North-Holland, 1973.
-/

section

open ArithmeticFunction
open Filter Real
open scoped omega Omega

namespace Erdos535

/-- No `r`-subset has constant pairwise GCD with coprime quotients. -/
def NoConstantPairwiseGcdCoprimeSubsets (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = r →
    ¬ (∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
      ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1)

/--
All elements of `A` are positive and have exactly `k` prime factors,
counted with multiplicity.

Erdős [Er73] explains that Abbott pointed out the ordinary sunflower conjecture
does not seem to suffice for Problem 535; the corrected stronger auxiliary
statement uses $Ω$, not $ω$.
-/
def AllBigOmega (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ Ω a = k

/-- `f r N` is the maximum size of a subset `A ⊆ {1,…,N}` such that no `r`-element
subset of `A` has constant pairwise GCD. -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}

end Erdos535
