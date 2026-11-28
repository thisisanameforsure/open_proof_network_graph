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
import Defs.AnalysisEquidistributionModOne
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.NumberTheoryPisotNumber

/-! Ported mechanically from `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_61.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Bugeaud Collection of Conjectures and Open Questions: Pisot orbits on the Cantor set

Problem 10.61, proposed by Mendès France [MF67, Problème 1, p. 41]. For a Pisot number
$\alpha > 2$ put
$$C(\alpha) = \left\{ (\alpha - 1) \sum_{k \ge 1} \varepsilon_k \alpha^{-k} :
\varepsilon_k \in \{0, 1\} \right\}.$$
The problem asks to prove that $(\xi \alpha^n)_{n \ge 1}$ is not uniformly distributed
modulo one for any $\xi \in C(\alpha)$. In the language of [MF67] this reads
$C(\alpha) \cap B(\alpha) = \emptyset$, where $B(\alpha)$ is the set of $\xi$ for which
$(\xi \alpha^n)$ is uniformly distributed modulo one.

The problem is open. It is easy for an integer base and settled for two quadratic
$\alpha$; the general Pisot case is what remains. [Ste26] reduces it to a statement about
shift-invariant measures of the full two-shift, and proves that every true instance admits
a finite certificate, so the difficulty is uniformity in $\alpha$ rather than any single
$\alpha$. The variants below state the criterion and the instances of [Ste26] that concern
Problem 10.61 directly; the reduction itself is not stated here, since it needs the symbolic
model.

Deleting the term $n = 0$ does not change uniform distribution modulo one, so the
statements indexed from $n = 1$ agree with the ones of [Ste26], which are indexed from
$n = 0$. Where an orbit is confined away from an interval the stronger form, for every
$n \ge 0$, is stated.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10, Problem 10.61, p. 222.
  - [MF67] Mendès France, Michel. "Nombres normaux. Applications aux fonctions
    pseudo-aléatoires." Journal d'Analyse Mathématique 20 (1967): 1-56.
  - [Kok35] Koksma, Jurjen F. "Ein mengentheoretischer Satz über die Gleichverteilung
    modulo Eins." Compositio Mathematica 2 (1935): 250-258.
  - [Ste26] Stephan, Ralf. "Criteria for the non-equidistribution of $(\xi \alpha^n)$ on
    the Cantor set $C(\alpha)$." Preprint, 2026.
    https://doi.org/10.13140/RG.2.2.13923.52001
-/

section

namespace Bugeaud61

/--
The point of $C(\alpha)$ with digit sequence $\varepsilon$, that is
$(\alpha - 1) \sum_{k \ge 1} \varepsilon_k \alpha^{-k}$.
-/
noncomputable def cantorPoint (α : ℝ) (ε : ℕ → Bool) : ℝ :=
  (α - 1) * ∑' k : ℕ, (if ε k then (1 : ℝ) else 0) * α⁻¹ ^ (k + 1)

/--
The set $C(\alpha)$ of Problem 10.61. For $\alpha > 2$ it is a Cantor set of Hausdorff
dimension $\log 2 / \log \alpha < 1$, normalised so that $0$ is its least and $1$ its
greatest element.
-/
noncomputable def pisotCantorSet (α : ℝ) : Set ℝ := Set.range (cantorPoint α)

/--
The Route A exponent $A(\alpha) = \log 2 / \log \alpha + \log 2 / \log(1 / \rho)$ of
[Ste26], where $\rho$ is the largest modulus of a conjugate of $\alpha$ other than
$\alpha$ itself. It is the sum of the box dimensions of $C(\alpha)$ and of the window in
which the conjugate contributions live.
-/
noncomputable def routeAExponent (α ρ : ℝ) : ℝ :=
  Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹

end Bugeaud61
