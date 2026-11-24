import Mathlib
import Nodes.«spec-9ab4bdf6».Context

/-- A third-position condition on the calm points of the hole `variant-cce9b284--h6`, the first
step of condition N1 of annex `eaaf51ac…` on that hole: for every `m ≥ 1092` with `m + 1`
prime, either `m + 3` has at most four divisors `a` with `20 < a < m`, or the weighted divisor
count `G(m) = ∑_{i ≥ 0} 2^{-(i+1)} #{a : 20 < a < m, a ∣ m + i + 1}` of that hole exceeds
`99/100`. With `spec-23231427` (a calm `m ≥ 1092` has `m + 1` prime), every calm point has at
most four divisors of `m + 3` in `(20, m)`. -/
theorem Opn.erdos_257_calm_point_third_position :
    ∀ m : ℕ, 1092 ≤ m → (m + 1).Prime →
      {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 3}.ncard ≤ 4 ∨
        (99 / 100 : ℝ) < ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) *
          ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) := by
  -- the divisor sets are finite, inside `[0, m)`
  have hfin : ∀ m n : ℕ, ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ n} : Set ℕ).Finite :=
    fun m n => (Set.finite_Iio m).subset (fun _ ha => ha.2.1)
  have hcardle : ∀ m n : ℕ, ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ n} : Set ℕ).ncard ≤ m := by
    intro m n
    calc ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ n} : Set ℕ).ncard ≤ (Set.Iio m).ncard :=
          Set.ncard_le_ncard (fun _ ha => ha.2.1) (Set.finite_Iio m)
      _ = m := by simp
  -- one member gives a count of at least one, two distinct members at least two
  have hone : ∀ {m n x : ℕ}, (20 < x ∧ x < m ∧ x ∣ n) →
      (1 : ℝ) ≤ (({a : ℕ | 20 < a ∧ a < m ∧ a ∣ n} : Set ℕ).ncard : ℝ) := by
    intro m n x hx
    have h : ({x} : Set ℕ) ⊆ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ n} := by
      intro a ha
      rcases ha with rfl
      exact hx
    have := Set.ncard_le_ncard h (hfin m n)
    rw [Set.ncard_singleton] at this
    exact_mod_cast this
  have htwo : ∀ {m n x y : ℕ}, x ≠ y → (20 < x ∧ x < m ∧ x ∣ n) → (20 < y ∧ y < m ∧ y ∣ n) →
      (2 : ℝ) ≤ (({a : ℕ | 20 < a ∧ a < m ∧ a ∣ n} : Set ℕ).ncard : ℝ) := by
    intro m n x y hxy hx hy
    have h : ({x, y} : Set ℕ) ⊆ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ n} := by
      intro a ha
      rcases ha with rfl | rfl
      · exact hx
      · exact hy
    have := Set.ncard_le_ncard h (hfin m n)
    rw [Set.ncard_pair hxy] at this
    exact_mod_cast this
  intro m hm hp
  by_cases h3 : {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 3}.ncard ≤ 4
  · exact Or.inl h3
  right
  push Not at h3
  set f : ℕ → ℝ := fun i => (1 / 2 : ℝ) ^ (i + 1) *
      ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) with hf
  have hnn : ∀ i, 0 ≤ f i := fun i => by positivity
  -- each term is at most `m / 2^(i+1)`, so the series converges
  have hsum : Summable f := by
    refine Summable.of_nonneg_of_le hnn (fun i => ?_)
      ((summable_geometric_two.mul_right (1 / 2 : ℝ)).mul_right (m : ℝ))
    simp only [hf]
    have hc : (({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1} : Set ℕ).ncard : ℝ) ≤ m := by
      exact_mod_cast hcardle m (m + i + 1)
    have : (1 / 2 : ℝ) ^ (i + 1) = (1 / 2) ^ i * (1 / 2) := pow_succ _ _
    rw [this]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  -- the series is at least its first four terms
  have hle : ∑ i ∈ Finset.range 4, f i ≤ ∑' i, f i :=
    hsum.sum_le_tsum _ (fun i _ => hnn i)
  -- the term at `i = 2` (that is, `m + 3`) has count at least five
  have h2 : (5 : ℝ) ≤ (({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 2 + 1} : Set ℕ).ncard : ℝ) := by
    have : m + 2 + 1 = m + 3 := by ring
    rw [this]; exact_mod_cast h3
  -- `m` is even, since `m + 1` is an odd prime
  have hodd : Odd (m + 1) := hp.odd_of_ne_two (by omega)
  have heven : Even m := by
    rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  obtain ⟨k, hk⟩ := heven
  have h0 : 0 ≤ f 0 := hnn 0
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- `m = 4j`: `(m+2)/2` divides `m + 2`; `(m+4)/2` and `(m+4)/4` divide `m + 4`
    have hm4 : m = 4 * j := by omega
    have h1 : (1 : ℝ) ≤ (({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 1 + 1} : Set ℕ).ncard : ℝ) :=
      hone (x := 2 * j + 1) ⟨by omega, by omega, ⟨2, by omega⟩⟩
    have h4 : (2 : ℝ) ≤ (({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 3 + 1} : Set ℕ).ncard : ℝ) :=
      htwo (x := 2 * j + 2) (y := j + 1) (by omega)
        ⟨by omega, by omega, ⟨2, by omega⟩⟩ ⟨by omega, by omega, ⟨4, by omega⟩⟩
    -- 1/4 + 5/8 + 2/16 = 1 > 99/100
    have : (99 / 100 : ℝ) < ∑ i ∈ Finset.range 4, f i := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf] at h0 ⊢
      norm_num at h0 ⊢
      nlinarith [h1, h2, h4, h0]
    linarith
  · -- `m = 4j + 2`: `(m+2)/2` and `(m+2)/4` divide `m + 2`
    have hm4 : m = 4 * j + 2 := by omega
    have h1 : (2 : ℝ) ≤ (({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 1 + 1} : Set ℕ).ncard : ℝ) :=
      htwo (x := 2 * j + 2) (y := j + 1) (by omega)
        ⟨by omega, by omega, ⟨2, by omega⟩⟩ ⟨by omega, by omega, ⟨4, by omega⟩⟩
    have h4 : 0 ≤ f 3 := hnn 3
    -- 2/4 + 5/8 = 9/8 > 99/100
    have : (99 / 100 : ℝ) < ∑ i ∈ Finset.range 4, f i := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf] at h0 h4 ⊢
      norm_num at h0 h4 ⊢
      nlinarith [h1, h2, h4, h0]
    linarith
