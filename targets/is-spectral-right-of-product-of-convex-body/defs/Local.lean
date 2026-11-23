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
import Defs.AnalysisFourierSpectralSets
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses

/-! Ported mechanically from `FormalConjectures/Arxiv/2209.04540/SpectralSetsAndWeakTiling.lean` at registry commit d8d031d4998c78575159ccab9a7a9e95ce043883 (google-deepmind/formal-conjectures, Apache-2.0) by gate/tools/wave.py (F14-T19): the file's own definitions, without the conjectures it states and their tests. The module syntax is stripped so the gate elaborates it under `import Mathlib`; nothing else is changed. -/

/-!
# Spectral sets and weak tiling

This file formalizes Problems 7.1 and 7.2 from Kolountzakis, Lev, and Matolcsi.

*References:*
- [KLM2023] Mihail N. Kolountzakis, Nir Lev, and Máté Matolcsi,
  [Spectral sets and weak tiling](https://arxiv.org/abs/2209.04540).
- [GL16] Rachel Greenfeld and Nir Lev, Spectrality and tiling by cylindric domains,
  *Journal of Functional Analysis* 271 (2016), 2808–2821.
- [GL20] Rachel Greenfeld and Nir Lev, Spectrality of product domains and Fuglede's conjecture
  for convex polytopes, *Journal d'Analyse Mathématique* 140 (2020), 409–441.
- [Ki26] Kenta Kitamura, A Lean proof of Problem 7.2 of Kolountzakis–Lev–Matolcsi in dimension
  three, [GitHub repository](https://github.com/KitaKen1/klm-7-2-spectral-product-3d) (2026).
-/

section

open MeasureTheory

namespace NowhereDenseSpectralSet

end NowhereDenseSpectralSet

namespace SpectralSetProduct

/-- The product $A \times B$, represented by consecutive coordinate blocks. -/
def productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) :=
  {x | (fun i ↦ x (Fin.castAdd m i)) ∈ A ∧ (fun j ↦ x (Fin.natAdd n j)) ∈ B}

/-- Spectrality of a product with an `n`-dimensional convex body forces spectrality of its
bounded, measurable `m`-dimensional right factor.

Following [KLM2023, §1.1], a convex body is a compact convex set with nonempty interior;
Mathlib's `ConvexBody` does not require the latter, so it is imposed explicitly here. -/
def spectralProductImpliesRightSpectral (n m : ℕ) : Prop :=
  ∀ (A : ConvexBody (Fin n → ℝ)) (B : Set (Fin m → ℝ)),
    (interior (A : Set (Fin n → ℝ))).Nonempty →
    Bornology.IsBounded B → MeasurableSet B →
      isSpectral (productSet (A : Set (Fin n → ℝ)) B) → isSpectral B

end SpectralSetProduct
