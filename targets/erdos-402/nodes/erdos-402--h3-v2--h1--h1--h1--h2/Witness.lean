import Mathlib
import Nodes.«erdos-402--h3-v2--h1--h1--h1--h2».Context
open Filter

/-! The witness slot for a hole (D-29, F07-R6). Replace `sorry` with an instance
satisfying this statement's hypotheses; until then the node is blocked. -/

theorem witness : ∃ (B : Finset ℕ),
  (0 : ℕ) ∉ B ∧
    B.Nonempty ∧
      B.gcd id = (1 : ℕ) ∧
        ¬Nat.Prime B.card ∧
          (∀ (q : ℕ), Nat.Prime q → B.card ≠ q + (1 : ℕ)) ∧
            (∀ a ∈ B, ∀ b ∈ B, a ≤ B.card * a.gcd b) ∧ ∀ a ∈ B, ∀ (p k : ℕ), Nat.Prime p → p ^ k ∣ a → p ^ k < B.card := by
  sorry
