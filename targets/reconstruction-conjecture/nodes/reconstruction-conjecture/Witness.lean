open ReconstructionConjecture

/-! Non-vacuity witness (D-4 step 7): the empty graph on three vertices is hypomorphic to itself through the identity, each vertex-deleted subgraph matched by the identity isomorphism. -/

theorem witness : ∃ (V W : Type) (inst : Fintype V) (inst : Fintype W) (G : SimpleGraph V)
    (H : SimpleGraph W), 3 ≤ Fintype.card V ∧ Hypomorphic G H :=
  ⟨Fin 3, Fin 3, inferInstance, inferInstance, (⊥ : SimpleGraph (Fin 3)),
    (⊥ : SimpleGraph (Fin 3)), by simp,
    ⟨Equiv.refl (Fin 3), fun v => ⟨by exact SimpleGraph.Iso.refl⟩⟩⟩
