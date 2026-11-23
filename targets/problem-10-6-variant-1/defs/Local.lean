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

/-! Ported mechanically from `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Bugeaud Collection of Conjectures and Open Questions: Rapidly Increasing Sequences Dense Modulo One

Problem 10.6 asks for a "very rapidly increasing" sequence $(m_n)_{n \ge 1}$ of positive
integers with $(\{\xi m_n\})_{n \ge 1}$ dense modulo one for every irrational $\xi$. The
informal phrase admits several readings, and they are not equivalent:

* a lower bound on the size of the terms, $m_n \ge f(n)$;
* an upper bound on the counting function of $\{m_n\}$;
* a lower bound on the consecutive ratios, $m_{n+1}/m_n \ge 1 + c/\log n$.

The first two readings are vacuous, and `exists_dense_of_growth_and_sparsity` below says so: a
sequence built from runs of consecutive integers is dense modulo one for every irrational $\xi$
by an elementary argument, and the runs may be placed so that its terms dominate any prescribed
$f$ while its counting function stays below $(\log\log N)^2$. In the subexponential range the
growth half is a special case of [Bos83, Thm. 1.5], which produces such a sequence in any
prescribed subexponential corridor and in the stronger uniform-distribution form; the sparsity
half sits below the $\log N$ floor that every sublacunary sequence obeys, and so below the
counting function of [Kat16, Cor. 4.10]. Consequently `problem_10_6_variant_2`, which asks only
for intermediate growth, is not open.

The third reading is `IsGenuinelySublacunary`, and it is the only one with content: it implies
the first (`hasIntermediateGrowth_of_isGenuinelySublacunary`), and it is not answered by runs,
since inside a run $m_{n+1} - m_n = 1$. That reading is `problem_10_6_variant_1`, which remains
open; [Kat16, Cor. 4.9] gives a universally densifying sequence of multiplicative shape
$\{2^n 3^e\}$ whose ratio behaviour reduces the question to a Diophantine statement about
$\log_2 3$.

The three statements that need a long proof carry a `formal_proof` link to the version of this
file that contains it: the construction by runs, its counting function, and the growth estimate
behind `hasIntermediateGrowth_of_isGenuinelySublacunary`.

*References:*
  - [Bos83] Boshernitzan, Michael D. "Homogeneously distributed sequences and Poincaré sequences
    of integers of sublacunary growth." Monatshefte für Mathematik 96.3 (1983): 173-181.
  - [Bos94] Boshernitzan, Michael D. "Density modulo 1 of dilations of sublacunary sequences."
    Advances in Mathematics 108.1 (1994): 104-117.
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Fur67] Furstenberg, H. "Disjointness in ergodic theory, minimal sets, and a problem
    in diophantine approximation". Math. Systems Theory 1, 1–49 (1967).
  - [Kat16] Katz, Asaf. "Generalizations of Furstenberg's Diophantine result."
    arXiv:1607.00670 (2016).
  - [Mat80] de Mathan, Bernard. "Numbers contravening a condition in density modulo 1."
    Acta Mathematica Hungarica 36.3-4 (1980): 237-241.
  - [Pol79] Pollington, Andrew Douglas. "On the density of sequence $\{n_ {k}\xi\} $."
    Illinois Journal of Mathematics 23.4 (1979): 511-515.
-/

section

namespace Bugeaud06

open Filter

/- ## Two theorems from the literature -/

/- ## The counting function -/

/-- The counting function $\pi_A(N) = \#(A \cap [0, N])$ of the range $A$ of `m`. The outer
`Finset.range (N + 1)` is harmless for a strictly increasing `m`, since then $n \le m_n$. -/
def countingFn (m : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun n => m n ≤ N).card

/- ## Growth and sparsity alone are not a restriction -/

/- ## The ratio-floor reading -/

/-- The sequence defined by $m_0 = 2$ and $m_{n+1} = \lceil m_n (1 + 1/\log n) \rceil$. -/
noncomputable def mSeq : ℕ → ℕ
  | 0 => 2
  | (n + 1) => ⌈(mSeq n : ℝ) * (1 + 1 / Real.log n)⌉₊

/-- The sequence $m$ eventually grows at least geometrically with a logarithmic correction. -/
def IsGenuinelySublacunary (m : ℕ → ℕ) : Prop :=
  ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, (1 + c / Real.log n) ≤ (m (n+1) : ℝ) / m n

/-- The sequence $m$ eventually grows at least as fast as $\exp(n^{\alpha})$, i.e., super-exponential
growth when $\alpha > 1$, and stretched-exponential when $0 < \alpha < 1$. -/
def HasIntermediateGrowth (α : ℝ) (m : ℕ → ℕ) : Prop :=
  ∀ᶠ (n : ℕ) in atTop, Real.exp ((n : ℝ) ^ α) ≤ m n

/- ## The problem -/

end Bugeaud06
