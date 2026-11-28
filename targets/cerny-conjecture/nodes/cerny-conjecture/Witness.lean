open Filter

/-! Non-vacuity witness (D-4 step 7): the one-state automaton over a one-letter alphabet is synchronized by the empty word. -/
theorem witness.{u_1, u_2} : ∃ (α : Type u_1) (σ : Type u_2) (inst : Fintype σ) (M : DFA α σ), M.IsSynchronizing :=
  ⟨PUnit, PUnit, inferInstance, ⟨fun _ _ => PUnit.unit, PUnit.unit, Set.univ⟩, ⟨[], PUnit.unit, fun _ => rfl⟩⟩
