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

/-! Erdős problem 257: Let $A\subseteq\mathbb{N}$ be an infinite set. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/257.lean at c7f31d5fd3d2ca3d69979f2d213eb9b58fe956ae, Apache-2.0); the registry states a yes/no question as `answer(sorry) ↔ P`; this states P, its affirmative reading (F11-Q24). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

theorem Opn.erdos_257 :
    ∀ (A : Set ℕ), A.Infinite →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  -- approach: case split on A over the fifteen special cases already on the graph, plus what is left
  -- licence: CC-BY-4.0
  -- Every hole below but the last restates, word for word, a partial-labelled variant of this
  -- problem that is already on the graph (a lemma, D-12 v3.38). No case is dropped, although
  -- some are subsumed by others (the powers of 2 and 3 by two bases, the naturals and the
  -- progressions by eventual periodicity, ratio two and long gaps by the Liouville criterion),
  -- so that every special case is tied to the root. The last hole is the exact complement.

  -- label: A = all naturals (Erdős 1948)
  -- claim: $\sum_{n \ge 1} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_naturals : Irrational (∑' n : ℕ, (1 : ℝ) / (2 ^ n - 1)) := sorry
  -- label: A an arithmetic progression (Erdős 1948, Borwein 1991)
  -- claim: $\forall a \ge 0,\ \forall d \ge 1:\ \sum_{n \ge 0} \frac{1}{2^{a+dn} - 1} \notin \mathbb{Q}$
  have h_progressions : ∀ a d : ℕ, 0 < d →
      Irrational (∑' m : {m : ℕ | ∃ n, m = a + d * n}, (1 : ℝ) / (2 ^ m.1 - 1)) := sorry
  -- label: A eventually periodic (Luca-Tachiya 2014)
  -- claim: $A \text{ infinite and eventually periodic} \Rightarrow \sum_{n \in A} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_periodic : ∀ A : Set ℕ, A.Infinite →
      (∃ p N : ℕ, 0 < p ∧ ∀ n, N ≤ n → (n ∈ A ↔ n + p ∈ A)) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A pairwise coprime with summable 1/a (Erdős 1968)
  -- claim: $A \text{ infinite, pairwise coprime},\ \sum_{a \in A} \frac{1}{a} < \infty \Rightarrow \sum_{n \in A} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_coprime : ∀ A : Set ℕ, A.Infinite → A.Pairwise Nat.Coprime →
      Summable (fun n : A => (1 : ℝ) / n.1) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A = the squarefree numbers (Duverney-Tachiya 2019)
  -- claim: $\sum_{n \text{ squarefree}} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_squarefree :
      Irrational (∑' n : {n : ℕ | Squarefree n}, (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A = the perfect k-th powers (Duverney-Tachiya 2019)
  -- claim: $\forall k \ge 1:\ \sum_{n \ge 1} \frac{1}{2^{n^k} - 1} \notin \mathbb{Q}$
  have h_powers : ∀ k : ℕ, 0 < k →
      Irrational (∑' m : {m : ℕ | ∃ n, m = n ^ k}, (1 : ℝ) / (2 ^ m.1 - 1)) := sorry
  -- label: A = the sums of two squares (Duverney-Tachiya 2019)
  -- claim: $\sum_{n = a^2 + b^2 \ge 1} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_two_squares :
      Irrational (∑' m : {m : ℕ | ∃ a b, m = a ^ 2 + b ^ 2}, (1 : ℝ) / (2 ^ m.1 - 1)) := sorry
  -- label: A = the primes (Tao-Teräväinen)
  -- claim: $\sum_{p \text{ prime}} \frac{1}{2^p - 1} \notin \mathbb{Q}$
  have h_primes :
      Irrational (∑' p : {p : ℕ | p.Prime}, (1 : ℝ) / (2 ^ p.1 - 1)) := sorry
  -- label: A eventually lacunary of ratio two
  -- claim: $0 \notin A \text{ infinite},\ (n < m \in A,\ n \ge N \Rightarrow m \ge 2n) \Rightarrow \sum_{n \in A} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_ratio_two : ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
      (∃ N : ℕ, ∀ m ∈ A, ∀ n ∈ A, N ≤ n → n < m → 2 * n ≤ m) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A meets Liouville's denominator criterion
  -- claim: $0 \notin A \text{ infinite},\ \forall C\ \exists m \in A\ \exists L:\ (2^a - 1) \mid L\ (a \in A,\ a < m),\ 2^C L \le 2^m \Rightarrow \sum_{n \in A} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_liouville : ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
      (∀ C : ℕ, ∃ m ∈ A, ∃ L : ℕ, 0 < L ∧ (∀ a ∈ A, a < m → 2 ^ a - 1 ∣ L) ∧ 2 ^ C * L ≤ 2 ^ m) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A with arbitrarily long gaps
  -- claim: $0 \notin A \text{ infinite},\ \forall C\ \exists m \in A:\ m \ge C + \sum_{a \in A,\ a < m} a \Rightarrow \sum_{n \in A} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_long_gaps : ∀ (A : Set ℕ), A.Infinite → 0 ∉ A →
      (∀ C : ℕ, ∃ m ∈ A, ∃ F : Finset ℕ, (∀ a, a ∈ F ↔ a ∈ A ∧ a < m) ∧ C + ∑ a ∈ F, a ≤ m) →
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A = the powers of 2 and the powers of 3
  -- claim: $\sum_{n \in \{2^k\} \cup \{3^k\}} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_two_and_three :
      Irrational (∑' n : ({n | ∃ k : ℕ, n = 2 ^ k} ∪ {n | ∃ k : ℕ, n = 3 ^ k} : Set ℕ),
        (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A = the powers of a and the powers of b
  -- claim: $2 \le a < b \Rightarrow \sum_{n \in \{a^k\} \cup \{b^k\}} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_two_bases : ∀ a b : ℕ, 2 ≤ a → a < b →
      Irrational (∑' n : ({n | ∃ k : ℕ, n = a ^ k} ∪ {n | ∃ k : ℕ, n = b ^ k} : Set ℕ),
        (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A = two divisibility chains of ratio at least 3
  -- claim: $x_j \mid x_{j+1},\ 3 x_j \le x_{j+1},\ \text{the same for } y \Rightarrow \sum_{n \in \{x_j\} \cup \{y_j\}} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_two_chains : ∀ x y : ℕ → ℕ, 0 < x 0 → 0 < y 0 →
      (∀ j, x j ∣ x (j + 1)) → (∀ j, y j ∣ y (j + 1)) →
      (∀ j, 3 * x j ≤ x (j + 1)) → (∀ j, 3 * y j ≤ y (j + 1)) →
      Irrational (∑' n : (Set.range x ∪ Set.range y : Set ℕ), (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: A = a union of r fast lacunary sequences
  -- claim: $c_i(j+1) \ge (2r+1)^{r+1} c_i(j)\ (i < r) \Rightarrow \sum_{n \in \bigcup_i c_i(\mathbb{N})} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  have h_lacunary_union : ∀ (r : ℕ) (c : Fin r → ℕ → ℕ), 0 < r → (∀ i, 0 < c i 0) →
      (∀ i j, (2 * r + 1) ^ (r + 1) * c i j ≤ c i (j + 1)) →
      Irrational (∑' n : (⋃ i, Set.range (c i) : Set ℕ), (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- label: every other infinite set (what is left)
  -- claim: $A \text{ infinite} \Rightarrow A \in \mathcal{C}_1 \cup \cdots \cup \mathcal{C}_{15} \lor \sum_{n \in A} \frac{1}{2^n - 1} \notin \mathbb{Q}$
  -- The fifteen classes are those of the holes above, in order; an infinite A in none of them
  -- has an irrational sum. Stated positively, as a disjunction, so that it can be witnessed.
  have h_rest : ∀ A : Set ℕ, A.Infinite →
      A = Set.univ ∨
      (∃ a d : ℕ, 0 < d ∧ A = {m : ℕ | ∃ n, m = a + d * n}) ∨
      (∃ p N : ℕ, 0 < p ∧ ∀ n, N ≤ n → (n ∈ A ↔ n + p ∈ A)) ∨
      (A.Pairwise Nat.Coprime ∧ Summable (fun n : A => (1 : ℝ) / n.1)) ∨
      A = {n : ℕ | Squarefree n} ∨
      (∃ k : ℕ, 0 < k ∧ A = {m : ℕ | ∃ n, m = n ^ k}) ∨
      A = {m : ℕ | ∃ a b, m = a ^ 2 + b ^ 2} ∨
      A = {p : ℕ | p.Prime} ∨
      (0 ∉ A ∧ ∃ N : ℕ, ∀ m ∈ A, ∀ n ∈ A, N ≤ n → n < m → 2 * n ≤ m) ∨
      (0 ∉ A ∧ ∀ C : ℕ, ∃ m ∈ A, ∃ L : ℕ, 0 < L ∧ (∀ a ∈ A, a < m → 2 ^ a - 1 ∣ L) ∧
        2 ^ C * L ≤ 2 ^ m) ∨
      (0 ∉ A ∧ ∀ C : ℕ, ∃ m ∈ A, ∃ F : Finset ℕ, (∀ a, a ∈ F ↔ a ∈ A ∧ a < m) ∧
        C + ∑ a ∈ F, a ≤ m) ∨
      A = ({n | ∃ k : ℕ, n = 2 ^ k} ∪ {n | ∃ k : ℕ, n = 3 ^ k} : Set ℕ) ∨
      (∃ a b : ℕ, 2 ≤ a ∧ a < b ∧
        A = ({n | ∃ k : ℕ, n = a ^ k} ∪ {n | ∃ k : ℕ, n = b ^ k} : Set ℕ)) ∨
      (∃ x y : ℕ → ℕ, 0 < x 0 ∧ 0 < y 0 ∧ (∀ j, x j ∣ x (j + 1)) ∧ (∀ j, y j ∣ y (j + 1)) ∧
        (∀ j, 3 * x j ≤ x (j + 1)) ∧ (∀ j, 3 * y j ≤ y (j + 1)) ∧
        A = (Set.range x ∪ Set.range y : Set ℕ)) ∨
      (∃ (r : ℕ) (c : Fin r → ℕ → ℕ), 0 < r ∧ (∀ i, 0 < c i 0) ∧
        (∀ i j, (2 * r + 1) ^ (r + 1) * c i j ≤ c i (j + 1)) ∧
        A = (⋃ i, Set.range (c i) : Set ℕ)) ∨
      Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := sorry
  -- The assembly: each class is one hole.
  intro A hA
  rcases h_rest A hA with h | ⟨a, d, hd, rfl⟩ | h | ⟨h1, h2⟩ | rfl | ⟨k, hk, rfl⟩ | rfl | rfl |
      ⟨h0, h⟩ | ⟨h0, h⟩ | ⟨h0, h⟩ | rfl | ⟨a, b, ha, hab, rfl⟩ |
      ⟨x, y, hx0, hy0, hxd, hyd, hx3, hy3, rfl⟩ | ⟨r, c, hr, hc0, hc, rfl⟩ | h
  · subst h
    rw [tsum_univ (f := fun n : ℕ => (1 : ℝ) / (2 ^ n - 1))]
    exact h_naturals
  · exact h_progressions a d hd
  · exact h_periodic A hA h
  · exact h_coprime A hA h1 h2
  · exact h_squarefree
  · exact h_powers k hk
  · exact h_two_squares
  · exact h_primes
  · exact h_ratio_two A hA h0 h
  · exact h_liouville A hA h0 h
  · exact h_long_gaps A hA h0 h
  · exact h_two_and_three
  · exact h_two_bases a b ha hab
  · exact h_two_chains x y hx0 hy0 hxd hyd hx3 hy3
  · exact h_lacunary_union r c hr hc0 hc
  · exact h
