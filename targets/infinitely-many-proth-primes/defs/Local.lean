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

/-! Ported mechanically from `FormalConjectures/Wikipedia/ProthPrime.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Proth primes

A *Proth number* is an integer $N = k \cdot 2^n + 1$ where $k$ is odd and $1 \le k < 2^n$. A Proth
number that is prime is called a *Proth prime*. Proth proved in 1878 that a Proth number $N$ is
prime if and only if $-1$ is an $((N - 1)/2)$-th power modulo $N$. It remains open whether
infinitely many Proth primes exist, and in particular whether any fixed odd multiplier such as
$k = 3$ produces infinitely many primes $3 \cdot 2^n + 1$.

*References:*
- [Wikipedia: Proth prime](https://en.wikipedia.org/wiki/Proth_prime)
- [Wikipedia: Thabit number](https://en.wikipedia.org/wiki/Thabit_number)
- [OEIS A080076](https://oeis.org/A080076)
- [OEIS A002253](https://oeis.org/A002253)
- [Pr1878] Proth, F. (1878). *Théorèmes sur les nombres premiers*, C. R. Acad. Sci. Paris 87, 926.
- [CP05] Crandall, R. and Pomerance, C. (2005). *Prime Numbers: A Computational Perspective*, 2nd
  ed., Springer, New York.
-/

section

namespace ProthPrime

/-- An integer $N$ is a **Proth number** if $N = k \cdot 2^n + 1$ for some odd $k$ and $n \ge 1$
with $k < 2^n$. -/
def IsProthNumber (N : ℕ) : Prop :=
  ∃ k n : ℕ, Odd k ∧ 1 ≤ n ∧ k < 2 ^ n ∧ N = k * 2 ^ n + 1

/-- A prime integer that is also a Proth number ([OEIS A080076](https://oeis.org/A080076)). -/
def IsProthPrime (N : ℕ) : Prop :=
  N.Prime ∧ IsProthNumber N

end ProthPrime
