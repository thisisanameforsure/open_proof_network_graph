/-! Non-vacuity witness (D-4 step 7) for a hole of the merged skeleton (D-12 #5, D-29).

The expected type is the hole's hypotheses, closed over the variables they mention (F01-R3):
a hole that inherits earlier lemmas as hypotheses can only be witnessed by discharging them, so
this file proves what it must. Lean core only — no Mathlib name appears — although the
statement's environment offers Mathlib, because a core proof is checkable anywhere the toolchain
is and cannot drift with a Mathlib rename.
-/

/-- Every number at least 2 has a prime divisor, over the graph's own definitions. Lean core
only: strong induction, and the classical extraction of a non-trivial divisor when `m` is not
prime. -/
theorem exists_prime_divisor : ∀ m : Nat, 2 ≤ m → ∃ p, Opn.IsPrime p ∧ Opn.Divides p m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm
    by_cases hp : Opn.IsPrime m
    · exact ⟨m, hp, ⟨1, (Nat.mul_one m).symm⟩⟩
    · have hex : ∃ d, Opn.Divides d m ∧ d ≠ 1 ∧ d ≠ m :=
        Classical.byContradiction fun hc =>
          hp ⟨hm, fun d hd =>
            Classical.byContradiction fun hne =>
              hc ⟨d, hd, fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩⟩
      obtain ⟨d, ⟨c, hdc⟩, hd1, hdm⟩ := hex
      have hd0 : d ≠ 0 := by
        intro h
        rw [h, Nat.zero_mul] at hdc
        omega
      have hdle : d ≤ m := Nat.le_of_dvd (by omega) ⟨c, hdc⟩
      have hd2 : 2 ≤ d := by omega
      have hdlt : d < m := by omega
      obtain ⟨p, hpp, a, hpa⟩ := ih d hdlt hd2
      exact ⟨p, hpp, ⟨a * c, by rw [hdc, hpa, Nat.mul_assoc]⟩⟩

/-- With `n = 0` the first hypothesis is vacuous: no `k` is both positive and at most 0.
And `d = m = 1`: 1 divides both 1 and 2. -/
theorem witness : ∃ n d m : Nat,
    (∀ k : Nat, 0 < k → k ≤ n → Opn.Divides k n.factorial) ∧
    (∀ m : Nat, 2 ≤ m → ∃ p, Opn.IsPrime p ∧ Opn.Divides p m) ∧
    Opn.Divides d m ∧ Opn.Divides d (m + 1) :=
  ⟨0, 1, 1, fun _ hk hle => absurd hk (by omega), exists_prime_divisor,
    ⟨1, by omega⟩, ⟨2, by omega⟩⟩
