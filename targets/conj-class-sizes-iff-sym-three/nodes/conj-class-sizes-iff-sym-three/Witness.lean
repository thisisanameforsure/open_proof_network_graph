open ConjClasses
open ConjugacyClassSizes

/-! Non-vacuity witness (D-4 step 7): S₃ is a nontrivial finite group whose conjugacy classes have distinct sizes (1, 3, 2); each class is computed as the finite set of conjugates and the comparison is decided. -/

theorem witness : ∃ (G : Type) (inst : Group G) (inst_1 : Fintype G),
    Nontrivial G ∧ HasDistinctConjClassSizes G := by
  refine ⟨Equiv.Perm (Fin 3), inferInstance, inferInstance,
    ⟨1, Equiv.swap 0 1, by decide⟩, ?_⟩
  have key : ∀ g : Equiv.Perm (Fin 3), conjClassCard (ConjClasses.mk g) =
      (Finset.univ.filter (fun h : Equiv.Perm (Fin 3) => ∃ c, c * h * c⁻¹ = g)).card := by
    intro g
    have hc : (ConjClasses.mk g).carrier =
        ↑(Finset.univ.filter (fun h : Equiv.Perm (Fin 3) => ∃ c, c * h * c⁻¹ = g)) := by
      ext h
      simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    unfold conjClassCard
    rw [hc, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hdec : ∀ g g' : Equiv.Perm (Fin 3),
      (Finset.univ.filter (fun h : Equiv.Perm (Fin 3) => ∃ c, c * h * c⁻¹ = g)).card =
      (Finset.univ.filter (fun h : Equiv.Perm (Fin 3) => ∃ c, c * h * c⁻¹ = g')).card →
      ∃ c, c * g * c⁻¹ = g' := by decide
  intro c d hcd
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  obtain ⟨g', rfl⟩ := ConjClasses.mk_surjective d
  rw [key, key] at hcd
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  exact hdec g g' hcd
