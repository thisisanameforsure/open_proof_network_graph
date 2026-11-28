open PebblingNumberConjecture

/-! Non-vacuity witness (D-4 step 7): two one-vertex graphs on `Unit`, each connected. -/

theorem witness : ∃ (V : Type) (inst : DecidableEq V) (W : Type) (inst : Fintype V)
    (inst : Fintype W) (inst : DecidableEq W) (G : SimpleGraph V) (H : SimpleGraph W),
    G.Connected ∧ H.Connected :=
  ⟨Unit, inferInstance, Unit, inferInstance, inferInstance, inferInstance, ⊥, ⊥,
   ⟨fun u v => by rw [Subsingleton.elim u v]⟩, ⟨fun u v => by rw [Subsingleton.elim u v]⟩⟩
