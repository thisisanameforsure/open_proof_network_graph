/-! Non-vacuity witness (D-4 step 7) for a hole of the merged skeleton (D-12 #5, D-29).

The expected type is the hole's hypotheses, closed over the variables they mention (F01-R3):
a hole that inherits earlier lemmas as hypotheses can only be witnessed by discharging them, so
this file proves what it must. Lean core only — no Mathlib name appears — although the
statement's environment offers Mathlib, because a core proof is checkable anywhere the toolchain
is and cannot drift with a Mathlib rename.
-/

/-- With `n = 0` the first hypothesis is vacuous: no `k` is both positive and at most 0. -/
theorem witness : ∃ n m : Nat,
    (∀ k : Nat, 0 < k → k ≤ n → Opn.Divides k n.factorial) ∧ 2 ≤ m :=
  ⟨0, 2, fun _ hk hle => absurd hk (by omega), by omega⟩
