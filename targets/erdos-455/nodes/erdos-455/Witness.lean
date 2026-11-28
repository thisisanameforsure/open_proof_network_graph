open Filter ENNReal

/-! Non-vacuity witness (D-4 step 7): the greedy sequence q 0 = 2, q 1 = 3, q (n+2) = the least prime ≥ 2·q (n+1) − q n, which is strictly increasing with non-decreasing gaps. -/
theorem witness : ∃ (q : ℕ → ℕ), StrictMono q ∧
    ∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n := by
  classical
  let step : ℕ × ℕ → ℕ × ℕ :=
    fun p => (p.2, Nat.find (Nat.exists_infinite_primes (2 * p.2 - p.1)))
  let f : ℕ → ℕ × ℕ := fun n => step^[n] (2, 3)
  have hf0 : f 0 = (2, 3) := rfl
  have hf : ∀ n, f (n + 1) = step (f n) := fun n => Function.iterate_succ_apply' step n (2, 3)
  have hstep1 : ∀ p : ℕ × ℕ, (step p).1 = p.2 := fun p => rfl
  have hprime : ∀ p : ℕ × ℕ, (step p).2.Prime :=
    fun p => (Nat.find_spec (Nat.exists_infinite_primes (2 * p.2 - p.1))).2
  have hge : ∀ p : ℕ × ℕ, 2 * p.2 - p.1 ≤ (step p).2 :=
    fun p => (Nat.find_spec (Nat.exists_infinite_primes (2 * p.2 - p.1))).1
  have hinv : ∀ n, (f n).1 < (f n).2 ∧ (f n).1.Prime ∧ (f n).2.Prime := by
    intro n
    induction n with
    | zero => rw [hf0]; exact ⟨by norm_num, Nat.prime_two, Nat.prime_three⟩
    | succ n ih =>
      rw [hf, hstep1]
      refine ⟨?_, ih.2.2, hprime _⟩
      have h1 := hge (f n)
      have h2 := ih.1
      omega
  refine ⟨fun n => (f n).1, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun n => ?_
    show (f n).1 < (f (n + 1)).1
    rw [hf, hstep1]
    exact (hinv n).1
  · intro n
    refine ⟨(hinv n).2.1, ?_⟩
    show (f (n + 1 + 1)).1 - (f (n + 1)).1 ≥ (f (n + 1)).1 - (f n).1
    rw [hf (n + 1), hf n]
    simp only [hstep1]
    have h1 := hge (f n)
    have h2 := (hinv n).1
    omega
