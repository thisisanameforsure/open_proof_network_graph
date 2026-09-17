import Mathlib

/-! Hole `borwein` of a merged partial proof, as a node (D-12 #5, D-29).
Revised statement (D-8): the parent assembly's own `have borwein` type, with the binder types and
the real-number ascriptions the gate-written statement had dropped. -/

theorem erdos_1050__h1 : ∃ a b : ℕ → ℤ,
    (∀ n : ℕ, (b n : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3)) - a n ≠ 0) ∧
    Filter.Tendsto
      (fun n : ℕ => (b n : ℝ) * (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 3) - 3)) - a n)
      Filter.atTop (nhds 0) := by
  sorry
