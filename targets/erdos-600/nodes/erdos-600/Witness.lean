open Filter
open scoped Topology
open scoped Classical
open Erdos600

/-! Non-vacuity witness (D-4 step 7): r = 2 satisfies 2 ≤ r. -/

theorem witness : ∃ (r : ℕ), (2 : ℕ) ≤ r := ⟨2, le_refl 2⟩
