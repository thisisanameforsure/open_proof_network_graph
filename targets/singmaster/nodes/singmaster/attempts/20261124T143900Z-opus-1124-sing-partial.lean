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
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local

/-! Singmaster's conjecture — imported from google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Singmaster.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Singmaster

theorem Opn.singmaster :
    ∃ (C : ℕ), ∀ (t : ℕ), t > 1 →
    (Singmaster.solutions t).Finite ∧ (Singmaster.solutions t).ncard ≤ C := by
  -- approach: symmetry and the two edges reduce the count to the interior left half of the triangle, 2 ≤ k ≤ n/2
  -- licence: CC-BY-4.0
  have hall : (∀ t : ℕ, (Singmaster.solutions t).Finite) ∧
      (∀ t C : ℕ, ({p : ℕ × ℕ | 2 ≤ p.2 ∧ 2 * p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = t}).ncard ≤ C →
        (Singmaster.solutions t).ncard ≤ 2 * C + 2) ∧
      (∃ C : ℕ, ∀ t : ℕ,
        ({p : ℕ × ℕ | 2 ≤ p.2 ∧ 2 * p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = t}).ncard ≤ C) := by
    refine ⟨?_, ?_, ?_⟩
    · -- label: finitely many solutions
      -- claim: $\{(n,k) : 1 \le k < n,\ \binom{n}{k} = t\}$ is finite for every $t$
      -- Since $\binom{n}{k} \ge n$ when $1 \le k < n$, every solution has $n \le t$.
      have h1 : ∀ t : ℕ, (Singmaster.solutions t).Finite := by sorry
      exact h1
    · -- label: reduction to the interior left half
      -- claim: $\#\{(n,k) : 2 \le k,\ 2k \le n,\ \binom{n}{k} = t\} \le C \Rightarrow N(t) \le 2C + 2$
      -- The edges k = 1 and k = n - 1 give only n = t; every other solution is in the left half or is the mirror image (n, n - k) of one there.
      have h2 : ∀ t C : ℕ,
          ({p : ℕ × ℕ | 2 ≤ p.2 ∧ 2 * p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = t}).ncard ≤ C →
          (Singmaster.solutions t).ncard ≤ 2 * C + 2 := by sorry
      exact h2
    · -- label: the interior left half is bounded
      -- claim: $\exists C\ \forall t,\ \#\{(n,k) : 2 \le k,\ 2k \le n,\ \binom{n}{k} = t\} \le C$
      -- Singmaster's conjecture in its normalised form: only binomial coefficients with 2 ≤ k ≤ n/2 are counted.
      have h3 : ∃ C : ℕ, ∀ t : ℕ,
          ({p : ℕ × ℕ | 2 ≤ p.2 ∧ 2 * p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = t}).ncard ≤ C := by sorry
      exact h3
  obtain ⟨hfin, hred, C, hC⟩ := hall
  exact ⟨2 * C + 2, fun t _ => ⟨hfin t, hred t C (hC t)⟩⟩
