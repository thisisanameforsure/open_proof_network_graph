import Mathlib
import Nodes.«variant-cce9b284».Context

/-- The refutation side of Erdős 257 stated as one existential: the Mersenne reciprocal sum of
some infinite set `A ⊆ ℕ` is a rational number. Any construction of a counterexample is a route
to this statement, whether it names its rational (`1/2`, the sibling variant) or settles on one
it does not name, as the repair walk below does. -/
theorem Opn.erdos_257_some_infinite_sum_is_rational :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ s : ℚ, ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) = s := by
  -- annex: 3888b5d8b8471c20c937b4d2e1f1ca46aa7384e83537626d48ec1a0a3cc0e3f8
  -- approach: calm points for some 2^-j, with the target 2^-j and the start N left open instead of 2^-20 and 1092: a stall at n+1 forces a weighted divisor count above 0.99 on (n, 2n-10]; it is at most the walk-free G_j, so a calm point (G_j <= 0.99) in every interval past N rules out every stall
  -- licence: CC-BY-4.0
  have hall : (∀ (L p : ℕ) (r : ℕ → ℝ), r 0 = (p : ℝ) / 2 ^ L → (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) → ∀ n m : ℕ, L ≤ n → n < m → m + 10 ≤ 2 * n → (r (n + 1) < (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) ∧ (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + i) - 1)) < r (n + 1)) → (99 / 100 : ℝ) < ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | 1 ≤ a ∧ a ≤ n ∧ (1 : ℝ) / ((2 : ℝ) ^ a - 1) ≤ r a ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ)) ∧ (∀ (j : ℕ) (r : ℕ → ℝ), r 0 = 1 / 2 ^ j → (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) → ∀ n m : ℕ, n < m → (∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | 1 ≤ a ∧ a ≤ n ∧ (1 : ℝ) / ((2 : ℝ) ^ a - 1) ≤ r a ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ)) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | j < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ)) ∧ (∃ j N : ℕ, 1 ≤ j ∧ j ≤ N ∧ (∀ r : ℕ → ℝ, r 0 = 1 / 2 ^ j → (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) → ∀ n : ℕ, n < N → ¬ (r (n + 1) < (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) ∧ (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + i) - 1)) < r (n + 1))) ∧ (∀ n : ℕ, N ≤ n → ∃ m : ℕ, n < m ∧ m + 10 ≤ 2 * n ∧ (∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | j < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ)) ≤ 99 / 100)) ∧ (∀ (x : ℝ) (r : ℕ → ℝ), 0 ≤ x → x ≤ 1 → r 0 = x → (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) → (∀ n : ℕ, ¬ (r (n + 1) < (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) ∧ (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + i) - 1)) < r (n + 1))) → ∑' a : {a : ℕ | 1 ≤ a ∧ (1 : ℝ) / ((2 : ℝ) ^ a - 1) ≤ r a}, (1 : ℝ) / (2 ^ a.1 - 1) = x) ∧ (∀ (j : ℕ), 1 ≤ j → ∀ A : Set ℕ, A.Finite → (∀ a ∈ A, 1 ≤ a) → ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) ≠ 1 / 2 ^ j) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · skip
      -- label: stall forces a large divisor count
      -- claim: $\text{stall at } n+1,\ x=p/2^L,\ L\le n<m,\ m+10\le 2n \;\Rightarrow\; W_n(m)>\tfrac{99}{100}$
      -- W_n(m) weights by 2^-(i+1) the divisors a <= n of m+i+1 chosen by the greedy walk of x.
      have h_stall_forces_count : ∀ (L p : ℕ) (r : ℕ → ℝ), r 0 = (p : ℝ) / 2 ^ L → (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) → ∀ n m : ℕ, L ≤ n → n < m → m + 10 ≤ 2 * n → (r (n + 1) < (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) ∧ (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + i) - 1)) < r (n + 1)) → (99 / 100 : ℝ) < ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | 1 ≤ a ∧ a ≤ n ∧ (1 : ℝ) / ((2 : ℝ) ^ a - 1) ≤ r a ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ) := by sorry
      exact h_stall_forces_count
    · skip
      -- label: the walk's count is at most the walk-free G_j
      -- claim: $x=2^{-j},\ n<m \;\Rightarrow\; W_n(m)\le G_j(m)$
      -- G_j(m) weights by 2^-(i+1) all divisors a of m+i+1 with j < a < m. Stated for every j.
      have h_count_le_calm_general : ∀ (j : ℕ) (r : ℕ → ℝ), r 0 = 1 / 2 ^ j → (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) → ∀ n m : ℕ, n < m → (∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | 1 ≤ a ∧ a ≤ n ∧ (1 : ℝ) / ((2 : ℝ) ^ a - 1) ≤ r a ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ)) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | j < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ) := by sorry
      exact h_count_le_calm_general
    · skip
      -- label: some 2^-j: no early stall, then calm points
      -- claim: $\exists j\ge 1,\ N\ge j:\ \text{no stall at } n+1 \text{ for } n<N,\ \text{ and } \forall n\ge N\ \exists m:\ n<m,\ m+10\le 2n,\ G_j(m)\le\tfrac{99}{100}$
      -- The walk is the greedy walk of 2^-j. The second part is about the divisors of m+1, m+2, ... only.
      have h_calm_chain_some_j : ∃ j N : ℕ, 1 ≤ j ∧ j ≤ N ∧ (∀ r : ℕ → ℝ, r 0 = 1 / 2 ^ j → (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) → ∀ n : ℕ, n < N → ¬ (r (n + 1) < (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) ∧ (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + i) - 1)) < r (n + 1))) ∧ (∀ n : ℕ, N ≤ n → ∃ m : ℕ, n < m ∧ m + 10 ≤ 2 * n ∧ (∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | j < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ)) ≤ 99 / 100) := by sorry
      exact h_calm_chain_some_j
    · skip
      -- label: with no stall the chosen set sums to x
      -- claim: $0\le x\le 1,\ \text{no stall at any step} \;\Rightarrow\; \sum_{a\ \text{chosen}}\frac{1}{2^a-1}=x$
      -- The greedy walk takes a when 1/(2^a-1) is at most the remainder.
      have h_no_stall_sums : ∀ (x : ℝ) (r : ℕ → ℝ), 0 ≤ x → x ≤ 1 → r 0 = x → (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) → (∀ n : ℕ, ¬ (r (n + 1) < (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) ∧ (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + i) - 1)) < r (n + 1))) → ∑' a : {a : ℕ | 1 ≤ a ∧ (1 : ℝ) / ((2 : ℝ) ^ a - 1) ≤ r a}, (1 : ℝ) / (2 ^ a.1 - 1) = x := by sorry
      exact h_no_stall_sums
    · skip
      -- label: no finite set sums to 2^-j
      -- claim: $j\ge 1,\ A\ \text{finite},\ 0\notin A \;\Rightarrow\; \sum_{a\in A}\frac{1}{2^a-1}\ne 2^{-j}$
      -- Finite sums have odd denominators.
      have h_finite_not_dyadic_general : ∀ (j : ℕ), 1 ≤ j → ∀ A : Set ℕ, A.Finite → (∀ a ∈ A, 1 ≤ a) → ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) ≠ 1 / 2 ^ j := by sorry
      exact h_finite_not_dyadic_general
  obtain ⟨h_stall_forces_count, h_count_le_calm_general, h_calm_chain_some_j,
    h_no_stall_sums, h_finite_not_dyadic_general⟩ := hall
  obtain ⟨j, N, hj1, hjN, h_early, h_calm⟩ := h_calm_chain_some_j
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → ℝ, r 0 = 1 / 2 ^ j ∧ (∀ k : ℕ, r (k + 1) = if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ r k then r k - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else r k) :=
    ⟨fun n => Nat.rec (1 / 2 ^ j : ℝ) (fun k acc => if 1 ≤ k ∧ (1 : ℝ) / ((2 : ℝ) ^ k - 1) ≤ acc then acc - (1 : ℝ) / ((2 : ℝ) ^ k - 1) else acc) n,
      rfl, fun k => rfl⟩
  have hnostall : ∀ n : ℕ, ¬ (r (n + 1) < (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1) ∧ (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2 + i) - 1)) < r (n + 1)) := by
    intro n hst
    by_cases hn : n < N
    · exact h_early r hr0 hrs n hn hst
    · obtain ⟨m, hm1, hm2, hm3⟩ := h_calm n (by omega)
      have h1 := h_stall_forces_count j 1 r (by rw [hr0]; norm_num) hrs n m (by omega) hm1 hm2 hst
      have h2 := h_count_le_calm_general j r hr0 hrs n m hm1
      linarith
  have hx0 : (0 : ℝ) ≤ 1 / 2 ^ j := by positivity
  have hx1 : (1 : ℝ) / 2 ^ j ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hsum := h_no_stall_sums (1 / 2 ^ j) r hx0 hx1 hr0 hrs hnostall
  refine ⟨{a : ℕ | 1 ≤ a ∧ (1 : ℝ) / ((2 : ℝ) ^ a - 1) ≤ r a}, ?_, (1 / 2 ^ j : ℚ), ?_⟩
  · by_contra hfin
    exact h_finite_not_dyadic_general j hj1 _ (Set.not_infinite.mp hfin) (fun a ha => ha.1) hsum
  · rw [hsum]
    norm_num
