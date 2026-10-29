import Mathlib

open Nat


theorem witness : ∃ x y : ℤ, y ^ 2 + y = x ^ 3 - x := ⟨0, 0, by norm_num⟩
