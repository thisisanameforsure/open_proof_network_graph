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

/-! Ported mechanically from `FormalConjectures/Paper/ZagierMZV.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Zagier's Conjecture on Multiple Zeta Values

*References:*
- [Za94] Zagier, Don. "Values of zeta functions and their applications."
  First European Congress of Mathematics Paris, July 6–10, 1992: Vol. II: Invited Lectures (Part 2). Basel: Birkhäuser Basel, 1994.
- [Co18] Combariza, Germán AG. "A few conjectures about the multiple zeta values."
  ACM Communications in Computer Algebra 52.1 (2018): 11-20.
- [Te02] T. Terasoma. Mixed Tate motives and multiple zeta values. Invent. Math., 149(2):339–369, 2002.
- [DG05] P. Deligne and A. Goncharov. Groupes fondamentaux motiviques de Tate mixte. Ann. Sci.
  Ecole Norm. Sup. (4), 38(1):1–56, 2005.
- [OEIS A000931](https://oeis.org/A000931)
-/

section

-- TODO(jgd) There are additional conjectures in Co18 which would be nice to formalize.

namespace ZagierMZV

open Finset BigOperators

/--
The multiple zeta value $\zeta(s_1, s_2, \ldots, s_k)$, defined as
$$\zeta(s_1, \ldots, s_k) = \sum_{n_1 > n_2 > \cdots > n_k > 0}
\frac{1}{n_1^{s_1} n_2^{s_2} \cdots n_k^{s_k}}.$$
The argument is a list of positive natural numbers. The value is well-defined (i.e. the series
converges) when the first entry is at least 2, but we define it for all inputs.
For the empty list, `multiZeta [] = 1` (the empty product convention).
-/
noncomputable def multiZeta : List ℕ → ℝ
  | [] => 1
  | s :: rest => ∑' n : ℕ, (1 / (n + 1 : ℝ) ^ s) * multiZeta.aux rest n
where
  /-- Auxiliary function for `multiZeta`: computes the inner sum
  $\sum_{n_2 > \cdots > n_k > 0, n_2 < \text{bound}} \frac{1}{n_2^{s_2} \cdots n_k^{s_k}}$. -/
  aux : List ℕ → ℕ → ℝ
  | [], _ => 1
  | s :: rest, bound => ∑ m ∈ Finset.range bound, (1 / (m + 1 : ℝ) ^ s) * aux rest m

/-- The *weight* of an MZV index $(s_1, \ldots, s_k)$ is $s_1 + \cdots + s_k$. -/
def weight (s : List ℕ) : ℕ := s.sum

/--
An MZV index is *admissible* if it is either empty or if the first entry is at least 2
and all entries are positive. The empty list convention ensures $\mathcal{Z}_0 = \mathbb{Q}$.
-/
def AdmissibleIndex : List ℕ → Prop
  | [] => True
  | s₁ :: rest => 1 < s₁ ∧ ∀ sᵢ ∈ rest, 0 < sᵢ

/-- The set of all MZV values of weight $n$. -/
def mzvSetOfWeight (n : ℕ) : Set ℝ :=
  multiZeta '' {s | AdmissibleIndex s ∧ weight s = n}

/-- The $\mathbb{Q}$-submodule of $\mathbb{R}$ spanned by all MZVs of weight $n$. -/
noncomputable def mzvSpanOfWeight (n : ℕ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (mzvSetOfWeight n)

/--
The conjectured Zagier dimension sequence $d_n$, defined by $d_0 = 1$, $d_1 = 0$, $d_2 = 1$,
and $d_n = d_{n-2} + d_{n-3}$ for $n \geq 3$.
-/
def zagierDim : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | (n + 3) => zagierDim (n + 1) + zagierDim n

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Tests
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end ZagierMZV
