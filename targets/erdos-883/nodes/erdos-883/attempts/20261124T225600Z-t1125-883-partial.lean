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
import Defs.CombinatoricsSimpleGraphCircumference
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataNatPrimeFinset
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local

/-! Erdős problem 883, part i: For $A\subseteq \{1,\ldots,n\}$ let $G(A)$ be the graph with vertex set $A$, where two integers are joined by an edge if they are coprime. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/883.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter
open scoped Classical
open Erdos883

private lemma erdos883_tri_mem {A : Finset ℕ} {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (cab : Nat.Coprime a b)
    (cbc : Nat.Coprime b c) (cac : Nat.Coprime a c) :
    3 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  let x : (A : Set ℕ) := ⟨a, ha⟩
  let y : (A : Set ℕ) := ⟨b, hb⟩
  let z : (A : Set ℕ) := ⟨c, hc⟩
  have hxy : (coprimeGraph.induce (A : Set ℕ)).Adj x y := by
    simp [x, y, coprimeGraph, SimpleGraph.fromRel_adj, hab]
    exact Or.inl cab
  have hyz : (coprimeGraph.induce (A : Set ℕ)).Adj y z := by
    simp [y, z, coprimeGraph, SimpleGraph.fromRel_adj, hbc]
    exact Or.inl cbc
  have hzx : (coprimeGraph.induce (A : Set ℕ)).Adj z x := by
    simp [z, x, coprimeGraph, SimpleGraph.fromRel_adj, Ne.symm hac]
    exact Or.inr cac
  refine ⟨⟨x, SimpleGraph.Walk.cons hxy (SimpleGraph.Walk.cons hyz
    (SimpleGraph.Walk.cons hzx SimpleGraph.Walk.nil)), ?_, rfl⟩, ⟨1, rfl⟩⟩
  have hxy' : x ≠ y := fun h => hab (congrArg Subtype.val h)
  have hyz' : y ≠ z := fun h => hbc (congrArg Subtype.val h)
  have hxz' : x ≠ z := fun h => hac (congrArg Subtype.val h)
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    simp [hyz', Ne.symm hxz', Ne.symm hxy']
  · simp [SimpleGraph.Walk.edges, hxy', hxz', hyz', Ne.symm hxy']

private lemma erdos883_cop (a b : ℕ) (hlt : a < b) (hd : b - a ≤ 4)
    (h2 : b - a = 2 ∨ b - a = 4 → a % 2 = 1) (h3 : b - a = 3 → a % 3 ≠ 0) :
    Nat.Coprime a b := by
  have hg : Nat.gcd a b ∣ b - a := Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b)
  have hga : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
  have hpos : 0 < b - a := by omega
  have hle : Nat.gcd a b ≤ b - a := Nat.le_of_dvd hpos hg
  unfold Nat.Coprime
  generalize Nat.gcd a b = g at hg hga hle ⊢
  generalize hd' : b - a = d at *
  interval_cases d <;> interval_cases g <;> simp_all <;> omega

private lemma erdos883_window (k : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc (6 * k + 2) (6 * k + 7)) (hcard : 5 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c := by
  have two_missing : ∀ x y, x ≠ y → x ∈ Finset.Icc (6 * k + 2) (6 * k + 7) →
      y ∈ Finset.Icc (6 * k + 2) (6 * k + 7) → x ∉ S → y ∉ S → False := by
    intro x y hxy hx hy hxS hyS
    have hsub : S ⊆ ((Finset.Icc (6 * k + 2) (6 * k + 7)).erase x).erase y := by
      intro z hz
      simp only [Finset.mem_erase]
      exact ⟨fun h => hyS (h ▸ hz), fun h => hxS (h ▸ hz), hS hz⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩),
      Finset.card_erase_of_mem hx, Nat.card_Icc] at h1
    omega
  have mem : ∀ x, 6 * k + 2 ≤ x → x ≤ 6 * k + 7 → x ∈ Finset.Icc (6 * k + 2) (6 * k + 7) := by
    intro x h1 h2
    simp only [Finset.mem_Icc]
    omega
  by_cases hb : 6 * k + 3 ∈ S
  · by_cases hc : 6 * k + 4 ∈ S
    · by_cases hd : 6 * k + 5 ∈ S
      · exact ⟨6 * k + 3, hb, 6 * k + 4, hc, 6 * k + 5, hd, by omega, by omega, by omega,
          erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega),
          erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega),
          erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega)⟩
      · have hf : 6 * k + 7 ∈ S := by
          by_contra hf
          exact two_missing (6 * k + 5) (6 * k + 7) (by omega) (mem _ (by omega) (by omega))
            (mem _ (by omega) (by omega)) hd hf
        exact ⟨6 * k + 3, hb, 6 * k + 4, hc, 6 * k + 7, hf, by omega, by omega, by omega,
          erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega),
          erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega),
          erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega)⟩
    · have hd : 6 * k + 5 ∈ S := by
        by_contra hd
        exact two_missing (6 * k + 4) (6 * k + 5) (by omega) (mem _ (by omega) (by omega))
          (mem _ (by omega) (by omega)) hc hd
      have he : 6 * k + 6 ∈ S := by
        by_contra he
        exact two_missing (6 * k + 4) (6 * k + 6) (by omega) (mem _ (by omega) (by omega))
          (mem _ (by omega) (by omega)) hc he
      have hf : 6 * k + 7 ∈ S := by
        by_contra hf
        exact two_missing (6 * k + 4) (6 * k + 7) (by omega) (mem _ (by omega) (by omega))
          (mem _ (by omega) (by omega)) hc hf
      exact ⟨6 * k + 5, hd, 6 * k + 6, he, 6 * k + 7, hf, by omega, by omega, by omega,
        erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega),
        erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega),
        erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega)⟩
  · have hd : 6 * k + 5 ∈ S := by
      by_contra hd
      exact two_missing (6 * k + 3) (6 * k + 5) (by omega) (mem _ (by omega) (by omega))
        (mem _ (by omega) (by omega)) hb hd
    have he : 6 * k + 6 ∈ S := by
      by_contra he
      exact two_missing (6 * k + 3) (6 * k + 6) (by omega) (mem _ (by omega) (by omega))
        (mem _ (by omega) (by omega)) hb he
    have hf : 6 * k + 7 ∈ S := by
      by_contra hf
      exact two_missing (6 * k + 3) (6 * k + 7) (by omega) (mem _ (by omega) (by omega))
        (mem _ (by omega) (by omega)) hb hf
    exact ⟨6 * k + 5, hd, 6 * k + 6, he, 6 * k + 7, hf, by omega, by omega, by omega,
      erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega),
      erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega),
      erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega)⟩

private lemma erdos883_split (S : Finset ℕ) (c : ℕ) :
    S.card ≤ (S.filter (· ≤ c)).card + (S.filter (fun x => ¬ x ≤ c)).card := by
  calc S.card ≤ (S.filter (· ≤ c) ∪ S.filter (fun x => ¬ x ≤ c)).card :=
        Finset.card_le_card (fun x hx => by by_cases h : x ≤ c <;> simp [hx, h] <;> omega)
    _ ≤ _ := Finset.card_union_le _ _

private lemma erdos883_blocks (q : ℕ) : ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 (6 * q + 1) →
    (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c → Nat.Coprime a b →
      Nat.Coprime b c → Nat.Coprime a c → False) → S.card ≤ 4 * q := by
  induction q with
  | zero =>
    intro S hS _
    have := Finset.card_le_card hS
    rw [Nat.card_Icc] at this
    omega
  | succ q ih =>
    intro S hS hN
    have h1 := ih (S.filter (· ≤ 6 * q + 1))
      (by
        intro x hx
        simp only [Finset.mem_filter] at hx
        have := hS hx.1
        simp only [Finset.mem_Icc] at this ⊢
        omega)
      (by
        intro a ha b hb c hc
        simp only [Finset.mem_filter] at ha hb hc
        exact hN a ha.1 b hb.1 c hc.1)
    have h2 : (S.filter (fun x => ¬ x ≤ 6 * q + 1)).card ≤ 4 := by
      by_contra hlt
      obtain ⟨a, ha, b, hb, c, hc, h⟩ := erdos883_window q (S.filter (fun x => ¬ x ≤ 6 * q + 1))
        (by
          intro x hx
          simp only [Finset.mem_filter] at hx
          have := hS hx.1
          simp only [Finset.mem_Icc] at this ⊢
          omega) (by omega)
      simp only [Finset.mem_filter] at ha hb hc
      exact hN a ha.1 b hb.1 c hc.1 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    have := erdos883_split S (6 * q + 1)
    omega

private lemma erdos883_no_one (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 2 n) (hn : 1 ≤ n)
    (hN : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c → Nat.Coprime a b →
      Nat.Coprime b c → Nat.Coprime a c → False) :
    S.card ≤ n / 2 + n / 3 - n / 6 := by
  set q := (n - 1) / 6 with hq
  have h1 := erdos883_blocks q (S.filter (· ≤ 6 * q + 1))
    (by
      intro x hx
      simp only [Finset.mem_filter] at hx
      have := hS hx.1
      simp only [Finset.mem_Icc] at this ⊢
      omega)
    (by
      intro a ha b hb c hc
      simp only [Finset.mem_filter] at ha hb hc
      exact hN a ha.1 b hb.1 c hc.1)
  have hsplit := erdos883_split S (6 * q + 1)
  set H := S.filter (fun x => ¬ x ≤ 6 * q + 1) with hH
  have hHsub : H ⊆ Finset.Icc (6 * q + 2) n := by
    intro x hx
    simp only [hH, Finset.mem_filter] at hx
    have := hS hx.1
    simp only [Finset.mem_Icc] at this ⊢
    omega
  have hHN : ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, a ≠ b → b ≠ c → a ≠ c → Nat.Coprime a b →
      Nat.Coprime b c → Nat.Coprime a c → False := by
    intro a ha b hb c hc
    simp only [hH, Finset.mem_filter] at ha hb hc
    exact hN a ha.1 b hb.1 c hc.1
  have hHc := Finset.card_le_card hHsub
  rw [Nat.card_Icc] at hHc
  have hr : n ≤ 6 * q + 6 := by omega
  by_cases h4 : n = 6 * q + 5
  · have hH3 : H.card ≤ 3 := by
      by_contra hlt
      have heq : H = Finset.Icc (6 * q + 2) n :=
        Finset.eq_of_subset_of_card_le hHsub (by rw [Nat.card_Icc]; omega)
      have m : ∀ x, 6 * q + 2 ≤ x → x ≤ n → x ∈ H := by
        intro x h1 h2
        rw [heq, Finset.mem_Icc]
        omega
      exact hHN (6 * q + 3) (m _ (by omega) (by omega)) (6 * q + 4) (m _ (by omega) (by omega))
        (6 * q + 5) (m _ (by omega) (by omega)) (by omega) (by omega) (by omega)
        (erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega))
        (erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega))
        (erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega))
    omega
  · by_cases h5 : n = 6 * q + 6
    · have hH4 : H.card ≤ 4 := by
        by_contra hlt
        obtain ⟨a, ha, b, hb, c, hc, h⟩ := erdos883_window q H
          (fun x hx => by
            have := hHsub hx
            simp only [Finset.mem_Icc] at this ⊢
            omega) (by omega)
        exact hHN a ha b hb c hc h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
      omega
    · omega

private lemma erdos883_pairs (j : ℕ) : ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 (2 * j + 1) →
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b → False) → S.card ≤ j := by
  induction j with
  | zero =>
    intro S hS _
    have := Finset.card_le_card hS
    rw [Nat.card_Icc] at this
    omega
  | succ j ih =>
    intro S hS hN
    have h1 := ih (S.filter (· ≤ 2 * j + 1))
      (by
        intro x hx
        simp only [Finset.mem_filter] at hx
        have := hS hx.1
        simp only [Finset.mem_Icc] at this ⊢
        omega)
      (by
        intro a ha b hb
        simp only [Finset.mem_filter] at ha hb
        exact hN a ha.1 b hb.1)
    have h2 : (S.filter (fun x => ¬ x ≤ 2 * j + 1)).card ≤ 1 := by
      by_contra hlt
      have hsub : S.filter (fun x => ¬ x ≤ 2 * j + 1) ⊆ Finset.Icc (2 * j + 2) (2 * j + 3) := by
        intro x hx
        simp only [Finset.mem_filter] at hx
        have := hS hx.1
        simp only [Finset.mem_Icc] at this ⊢
        omega
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Nat.card_Icc]; omega)
      have m : ∀ x, 2 * j + 2 ≤ x → x ≤ 2 * j + 3 → x ∈ S := by
        intro x h1 h2
        have : x ∈ S.filter (fun x => ¬ x ≤ 2 * j + 1) := by
          rw [heq, Finset.mem_Icc]
          omega
        exact (Finset.mem_filter.mp this).1
      exact hN (2 * j + 2) (m _ (by omega) (by omega)) (2 * j + 3) (m _ (by omega) (by omega))
        (by omega) (erdos883_cop _ _ (by omega) (by omega) (by omega) (by omega))
    have := erdos883_split S (2 * j + 1)
    omega

private lemma erdos883_h_tri (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) (hn : 6 ≤ n)
    (hcard : n / 2 + n / 3 - n / 6 < A.card) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c := by
  by_contra hcon
  have hN : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.Coprime a b →
      Nat.Coprime b c → Nat.Coprime a c → False :=
    fun a ha b hb c hc h1 h2 h3 h4 h5 h6 => hcon ⟨a, ha, b, hb, c, hc, h1, h2, h3, h4, h5, h6⟩
  by_cases h1 : 1 ∈ A
  · have hlow := erdos883_pairs ((n - 1) / 2) ((A.erase 1).filter (· ≤ 2 * ((n - 1) / 2) + 1))
      (by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_erase] at hx
        have := hA hx.1.2
        simp only [Finset.mem_Icc] at this ⊢
        omega)
      (by
        intro a ha b hb hab hc
        simp only [Finset.mem_filter, Finset.mem_erase] at ha hb
        exact hN 1 h1 a ha.1.2 b hb.1.2 (Ne.symm ha.1.1) hab (Ne.symm hb.1.1)
          (Nat.coprime_one_left a) hc (Nat.coprime_one_left b))
    have hhigh : ((A.erase 1).filter (fun x => ¬ x ≤ 2 * ((n - 1) / 2) + 1)).card ≤
        n / 2 - (n - 1) / 2 := by
      have hsub : (A.erase 1).filter (fun x => ¬ x ≤ 2 * ((n - 1) / 2) + 1) ⊆
          Finset.Icc (2 * ((n - 1) / 2) + 2) n := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_erase] at hx
        have := hA hx.1.2
        simp only [Finset.mem_Icc] at this ⊢
        omega
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have hsplit := erdos883_split (A.erase 1) (2 * ((n - 1) / 2) + 1)
    have hce := Finset.card_erase_of_mem h1
    omega
  · have hS : A ⊆ Finset.Icc 2 n := by
      intro x hx
      have := hA hx
      simp only [Finset.mem_Icc] at this ⊢
      refine ⟨?_, this.2⟩
      rcases Nat.lt_or_ge x 2 with h | h
      · exfalso
        have : x = 1 := by omega
        exact h1 (this ▸ hx)
      · exact h
    have := erdos883_no_one n A hS (by omega) hN
    omega

theorem Opn.erdos_883 :
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  -- approach: l = 3 is proved (blocks of six consecutive integers bound triangle-free sets by ⌊n/2⌋+⌊n/3⌋−⌊n/6⌋); odd l ≥ 5 is the open hole
  -- licence: CC-BY-4.0
  -- label: Odd cycles of length 5 to n/3 + 1
  -- claim: $A\subseteq\{1,\dots,n\},\ |A|>\lfloor n/2\rfloor+\lfloor n/3\rfloor-\lfloor n/6\rfloor,\ l\ \text{odd},\ 5\le l\le\lfloor n/3\rfloor+1\implies C_l\subseteq G(A)$
  have h_long : ∀ (n : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 5 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := sorry
  intro n A hA hcard l hl h3 hln
  rcases (show l = 3 ∨ 5 ≤ l by obtain ⟨k, rfl⟩ := hl; omega) with rfl | h5
  · obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac, cab, cbc, cac⟩ :=
      erdos883_h_tri n A hA (by omega) hcard
    exact erdos883_tri_mem ha hb hc hab hbc hac cab cbc cac
  · exact h_long n A hA hcard l hl h5 hln
