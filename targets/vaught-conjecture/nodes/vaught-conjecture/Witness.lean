open FirstOrder.Language
open VaughtConjecture

/-! Non-vacuity witness (D-4 step 7): the language with no symbols (at the statement's universes) is countable, and the complete theory of its one-point structure is complete. -/

theorem witness.{u_1, u_2} : ∃ (L : FirstOrder.Language.{u_1, u_2}) (T : L.Theory),
    Countable L.Symbols ∧ T.IsComplete := by
  let L : FirstOrder.Language.{u_1, u_2} := ⟨fun _ => PEmpty, fun _ => PEmpty⟩
  letI S : L.Structure PUnit.{1} :=
    ⟨fun f => PEmpty.elim (f : PEmpty), fun r => PEmpty.elim (r : PEmpty)⟩
  refine ⟨L, L.completeTheory PUnit.{1}, ?_,
    FirstOrder.Language.completeTheory.isComplete L PUnit.{1}⟩
  show Countable ((Σ _ : ℕ, PEmpty.{u_1 + 1}) ⊕ (Σ _ : ℕ, PEmpty.{u_2 + 1}))
  infer_instance
