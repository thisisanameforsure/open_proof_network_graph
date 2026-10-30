/-! A related variant of the tutorial node (D-30), proposed by the F08 smoke. -/

theorem OpnProp.and_left_of_and_swap : ∀ p q : Prop, p ∧ q → p := by
  -- approach: weaken the left conjunct to a disjunction with False, then discharge the False side
  -- licence: CC-BY-4.0
  intro p q h
  -- label: the left conjunct, or False
  -- claim: $p \land q \Rightarrow p \lor \mathrm{False}$
  have h₁ : p ∨ False := sorry
  exact h₁.elim id False.elim
