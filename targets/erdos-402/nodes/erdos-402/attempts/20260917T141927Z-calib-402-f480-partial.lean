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

/-! Erdős problem 402 (calibration): a known result — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/402.lean at c7f31d5fd3d2ca3d69979f2d213eb9b58fe956ae, Apache-2.0); restated by hand (binders before the colon: the witness is not `True`, write it by hand). A calibration target (Stages v3.17, F15-R14): a known result, drafted by docs/calibration_pool.py and read by the curator before intake. -/

open Filter

theorem Opn.erdos_402 :
    ∀ (A : Finset ℕ), 0 ∉ A → A.Nonempty → ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ) := by
  -- Skeleton of the Balasubramanian–Soundararajan / Szegedy argument for Graham's conjecture.
  -- Hole 1 (Farey structure): if every ratio a / gcd(a, b) over A is at most m, then every
  -- quotient a / b is a reduced fraction u / v with 1 ≤ u, v ≤ m.
  have h1 : ∀ (A : Finset ℕ) (m : ℕ), 0 ∉ A → (∀ a ∈ A, ∀ b ∈ A, a ≤ m * a.gcd b) →
      ∀ a ∈ A, ∀ b ∈ A, ∃ u v : ℕ, 0 < u ∧ u ≤ m ∧ 0 < v ∧ v ≤ m ∧ Nat.Coprime u v ∧
        a * v = b * u := sorry
  -- Hole 2 (reduction to primitive sets): the ratio a / gcd(a, b) is invariant under scaling, so
  -- the conclusion for every set of the same size with gcd 1 gives it for A.
  have h2 : ∀ A : Finset ℕ, 0 ∉ A → A.Nonempty →
      (∀ B : Finset ℕ, 0 ∉ B → B.card = A.card → B.gcd id = 1 →
        ∃ᵉ (a ∈ B) (b ∈ B), a.gcd b ≤ (a / B.card : ℚ)) →
      ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ) := sorry
  -- Hole 3 (the core, Balasubramanian–Soundararajan 1996; Szegedy 1986 and Zaharescu 1987 for
  -- large sets): a primitive set all of whose quotients are Farey fractions of order |A|
  -- satisfies Graham's bound.
  have h3 : ∀ A : Finset ℕ, 0 ∉ A → A.Nonempty → A.gcd id = 1 →
      (∀ a ∈ A, ∀ b ∈ A, ∃ u v : ℕ, 0 < u ∧ u ≤ A.card ∧ 0 < v ∧ v ≤ A.card ∧
        Nat.Coprime u v ∧ a * v = b * u) →
      ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ) := sorry
  -- Assembly: reduce to a primitive B of the same size; if the bound failed on B, every ratio
  -- would be below |B|, so B would have Farey structure of order |B|, and the core gives the
  -- bound after all.
  intro A hA hne
  refine h2 A hA hne ?_
  intro B hB hcard hg
  by_contra hcon
  push_neg at hcon
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact hne.card_pos
  have hbound : ∀ a ∈ B, ∀ b ∈ B, a ≤ B.card * a.gcd b := by
    intro a ha b hb
    have h := hcon a ha b hb
    have hpos : (0 : ℚ) < B.card := by exact_mod_cast hBne.card_pos
    have h' : (a : ℚ) < (a.gcd b : ℚ) * B.card := by
      first
        | exact (div_lt_iff₀ hpos).mp h
        | exact (div_lt_iff hpos).mp h
    rw [mul_comm] at h'
    have h'' : a < B.card * a.gcd b := by exact_mod_cast h'
    exact h''.le
  obtain ⟨a, ha, b, hb, hle⟩ := h3 B hB hBne hg (h1 B B.card hB hbound)
  exact absurd hle (not_le.mpr (hcon a ha b hb))
