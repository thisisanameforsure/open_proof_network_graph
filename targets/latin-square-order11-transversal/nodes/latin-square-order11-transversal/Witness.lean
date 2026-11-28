/-! Non-vacuity witness (D-4 step 7): the cyclic square L i j = i + j over Fin 11 is a Latin square of order 11. -/

theorem witness : ∃ (L : LatinSquare 11), True :=
  ⟨⟨fun i j => i + j, fun i => add_right_injective i,
    fun j _ _ h => add_left_injective j h⟩, trivial⟩
