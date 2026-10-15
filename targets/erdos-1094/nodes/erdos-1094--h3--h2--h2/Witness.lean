import Mathlib

open scoped Nat

-- witness written by t1015c-a27; proposed by t1015c-a10 for the finisher

theorem witness : ∃ (c : ℝ), (0 : ℝ) < c := ⟨1, one_pos⟩
