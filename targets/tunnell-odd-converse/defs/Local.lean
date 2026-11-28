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
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Wikipedia/CongruentNumber.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Congruent Number

A natural number $n$ is called a congruent number if there exists a right triangle with rational
sides $a$, $b$, and hypotenuse $c$ such that the area of the triangle is $\frac{1}{2}ab = n$.

*References:*
- [Wikipedia (Congruent number)](https://en.wikipedia.org/wiki/Congruent_number)
- [Wikipedia (Tunnell's theorem)](https://en.wikipedia.org/wiki/Tunnell%27s_theorem)
- [Keith Conrad's note](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/congnumber.pdf)
-/

section

namespace CongruentNumber

def congruentNumber (n : ℕ) : Prop :=
  ∃ (a b c : ℚ), a ^ 2 + b ^ 2 = c ^ 2 ∧ n = (2⁻¹ : ℚ) * a * b

/-
Tunnell's theorem:
Let $A_n$, $B_n$, $C_n$, and $D_n$ be the sets defined as follows:
- $A_n = \{(x, y, z) \in \mathbb{Z}^3 : n = 2x^2 + y^2 + 32z^2\}$
- $B_n = \{(x, y, z) \in \mathbb{Z}^3 : n = 2x^2 + y^2 + 8z^2\}$
- $C_n = \{(x, y, z) \in \mathbb{Z}^3 : n = 8x^2 + 2y^2 + 64z^2\}$
- $D_n = \{(x, y, z) \in \mathbb{Z}^3 : n = 8x^2 + 2y^2 + 16z^2\}$

If $n$ is a squarefree congruent number, then:
- If $n$ is odd, then $2 |A_n| = |B_n|$.
- If $n$ is even, then $2 |C_n| = |D_n|$.

Converse is true under the BSD conjecture.
-/

def A (n : ℕ) : Set (ℤ × ℤ × ℤ) := {(x, y, z) | n = 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2}
def B (n : ℕ) : Set (ℤ × ℤ × ℤ) := {(x, y, z) | n = 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2}
def C (n : ℕ) : Set (ℤ × ℤ × ℤ) := {(x, y, z) | n = 8 * x ^ 2 + 2 * y ^ 2 + 64 * z ^ 2}
def D (n : ℕ) : Set (ℤ × ℤ × ℤ) := {(x, y, z) | n = 8 * x ^ 2 + 2 * y ^ 2 + 16 * z ^ 2}

/-  Tunnell's theorem. -/

/-  Converse of Tunnell's theorem. -/

end CongruentNumber
