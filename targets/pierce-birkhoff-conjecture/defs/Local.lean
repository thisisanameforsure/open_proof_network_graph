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
import Defs.AlgebraOrderGroupPointwiseInterval
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsAdditiveVCDim
import Defs.CombinatoricsSetFamilyVCDim
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.ComputabilityTuringMachineBusyBeavers
import Defs.ComputabilityTuringMachinePostTuringMachine
import Defs.DataSetDensity
import Defs.DataSetInterval
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.OrderIntervalFinsetBasic
import Defs.OrderIntervalFinsetNat

/-! Ported mechanically from `FormalConjectures/Wikipedia/PierceBirkhoff.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Pierce–Birkhoff conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Pierce%E2%80%93Birkhoff_conjecture)

The Pierce-Birkhoff conjecture asserts that any piecewise-polynomial function can be expressed
as a maximum of finite minima of finite collections of polynomials. It was first stated in 1956
by Garrett Birkhoff and Richard S. Pierce, though the modern rigorous formulation is due to
Melvin Henriksen and John R. Isbell.

The conjecture has been proved for `n = 1` and `n = 2` by Louis Mahé.
-/

section

namespace PierceBirkhoff

/--
A set is semi-algebraic in `ℝⁿ` if it can be described by a finite union of sets, each defined by
finitely many simultaneous multivariate polynomial equations and strict inequalities.
-/
def IsSemiAlgebraic {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (ι : Type) (p₀ p₁ : ι → Finset (MvPolynomial (Fin n) ℝ)), Finite ι ∧
    S = ⋃ i, {x | (∀ p ∈ p₀ i, MvPolynomial.eval x p = 0) ∧
      ∀ p ∈ p₁ i, MvPolynomial.eval x p > 0}

/--
A set is semi-algebraic in `ℝ` if it can be described by a finite boolean combination
of polynomial equations and inequalities.
-/
def IsSemiAlgebraic₁ (S : Set ℝ) : Prop :=
  ∃ (ι₀ ι₁ : Type) (p₀ : ι₀ → Polynomial ℝ) (p₁ : ι₁ → Polynomial ℝ), Finite ι₀ ∧ Finite ι₁ ∧
    S = (⋃ i, {x | Polynomial.eval x (p₀ i) = 0}) ∪ ⋃ i, {x | Polynomial.eval x (p₁ i) > 0}

open scoped Polynomial

/--
A function `f : ℝⁿ → ℝ` is piecewise polynomial if there exists a finite covering of `ℝⁿ` by
closed semi-algebraic sets such that the restriction of `f` to each set in the covering is
polynomial.
-/
def IsPiecewiseMvPolynomial {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (ι : Type) (P : ι → Set (Fin n → ℝ))
    (g : ι → MvPolynomial (Fin n) ℝ),
    Finite ι ∧
    (∀ i, IsClosed (P i)) ∧
    (∀ i, IsSemiAlgebraic (P i)) ∧
    (⋃ i, P i) = Set.univ ∧
    ∀ᵉ (i : ι) (x ∈ P i), f x = MvPolynomial.eval x (g i)

/--
A function `f : ℝ → ℝ` is piecewise polynomial if there exists a finite covering of `ℝ` by
closed semi-algebraic sets such that the restriction of `f` to each set in the covering is
polynomial.
-/
def IsPiecewisePolynomial (f : ℝ → ℝ) : Prop :=
  ∃ (ι : Type) (P : ι → Set ℝ)
    (g : ι → Polynomial ℝ),
    Finite ι ∧
    (∀ (i : ι), IsClosed (P i)) ∧
    (∀ (i : ι), IsSemiAlgebraic₁ (P i)) ∧
    (⋃ (i : ι), P i) = Set.univ ∧
    ∀ᵉ (i : ι) (x ∈ P i), f x = Polynomial.eval x (g i)

end PierceBirkhoff
