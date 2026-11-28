open Arxiv.«2104.00502»

/-! Non-vacuity witness (D-4 step 7): the one-term sequence [1] is a Barker sequence (its entry is ±1 and it has no off-peak autocorrelations). -/

theorem witness : ∃ (a : List ℤ), IsBarkerSequence a := by
  refine ⟨[1], ?_, ?_⟩
  · intro x hx
    simp at hx
    exact Or.inl hx
  · intro k hk hk'
    simp at hk'
    omega
