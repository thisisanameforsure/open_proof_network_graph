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
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Arxiv/2607.08366/MinModulus.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Minimum modulus for the unique multiset-sum problem

*References:*
- [arxiv/2607.08366](https://arxiv.org/abs/2607.08366)
  **Minimum modulus for the unique multiset-sum problem**
  by *José A. R. Fonollosa*
- [jarfo/min-modulus](https://github.com/jarfo/min-modulus), the author's Lean development of
  the paper's Main Theorem. Section 7 of the paper describes it.

The paper's Main Theorem fixes the super-increasing set $\{2^k - 1\}$ and pins the least modulus
at which *it* is valid. Conjecture 1 says no other set of $n$ residues does better, and is open.
-/

section

open Finset

namespace Arxiv.«2607.08366»

variable {N : ℕ}

/-- `A` is *valid mod* `N` when the all-ones multiset is the only multiset of size `#A` drawn
from `A` whose sum matches `∑ a ∈ A, a`.

`m a` is how many copies of `a` the multiset uses. The all-ones multiset has `m a = 1` for
every `a ∈ A`; values outside `A` do not affect the sums. -/
def IsValidMod (A : Finset (ZMod N)) : Prop :=
  ∀ m : ZMod N → ℕ, ∑ a ∈ A, m a = #A → ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a →
    ∀ a ∈ A, m a = 1

/-- The candidate least modulus admitting a valid set of `n` residues, conjecturally
$2^n - 2^{\lfloor\log_2 n\rfloor}$. -/
def minModulus (n : ℕ) : ℕ := 2 ^ n - 2 ^ (Nat.log 2 n)

end Arxiv.«2607.08366»
