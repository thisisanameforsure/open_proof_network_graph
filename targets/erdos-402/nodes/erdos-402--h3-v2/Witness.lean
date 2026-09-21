import Mathlib

open Filter

theorem witness : ∃ A : Finset ℕ,
    (∀ (A : Finset ℕ) (m : ℕ), 0 ∉ A → (∀ a ∈ A, ∀ b ∈ A, a ≤ m * a.gcd b) →
      ∀ a ∈ A, ∀ b ∈ A, ∃ u v : ℕ, 0 < u ∧ u ≤ m ∧ 0 < v ∧ v ≤ m ∧ Nat.Coprime u v ∧ a * v = b * u) ∧
    (∀ (A : Finset ℕ), 0 ∉ A → A.Nonempty →
      (∀ (B : Finset ℕ), 0 ∉ B → B.card = A.card → B.gcd id = 1 →
        ∃ a ∈ B, ∃ b ∈ B, a.gcd b ≤ (a / B.card : ℚ)) →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ)) ∧
    0 ∉ A ∧ A.Nonempty ∧ A.gcd id = 1 ∧
    (∀ a ∈ A, ∀ b ∈ A, ∃ u v : ℕ, 0 < u ∧ u ≤ A.card ∧ 0 < v ∧ v ≤ A.card ∧ Nat.Coprime u v ∧ a * v = b * u) := by
  have hh1 : ∀ (A : Finset ℕ) (m : ℕ), 0 ∉ A → (∀ a ∈ A, ∀ b ∈ A, a ≤ m * a.gcd b) →
      ∀ a ∈ A, ∀ b ∈ A, ∃ u v : ℕ, 0 < u ∧ u ≤ m ∧ 0 < v ∧ v ≤ m ∧ Nat.Coprime u v ∧ a * v = b * u := by
      intro A m hA hbound a ha b hb
      have ha0 : a ≠ 0 := ne_of_mem_of_not_mem ha hA
      have hb0 : b ≠ 0 := ne_of_mem_of_not_mem hb hA
      have hd : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
      obtain ⟨u, hu⟩ := Nat.gcd_dvd_left a b
      obtain ⟨v, hv⟩ := Nat.gcd_dvd_right a b
      refine ⟨u, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply Nat.pos_of_ne_zero
        intro h0
        apply ha0
        rw [hu, h0, mul_zero]
      · have h1 : a.gcd b * u ≤ a.gcd b * m := by
          rw [← hu, mul_comm]
          exact hbound a ha b hb
        exact Nat.le_of_mul_le_mul_left h1 hd
      · apply Nat.pos_of_ne_zero
        intro h0
        apply hb0
        rw [hv, h0, mul_zero]
      · have h2 : a.gcd b * v ≤ a.gcd b * m := by
          rw [← hv, mul_comm, Nat.gcd_comm]
          exact hbound b hb a ha
        exact Nat.le_of_mul_le_mul_left h2 hd
      · have h3 : a.gcd b * u.gcd v = a.gcd b * 1 := by
          rw [← Nat.gcd_mul_left, ← hu, ← hv, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hd h3
      · calc a * v = a.gcd b * u * v := by rw [← hu]
          _ = a.gcd b * v * u := by ring
          _ = b * u := by rw [← hv]
  have hh2 : (∀ (A : Finset ℕ), 0 ∉ A → A.Nonempty →
      (∀ (B : Finset ℕ), 0 ∉ B → B.card = A.card → B.gcd id = 1 →
        ∃ a ∈ B, ∃ b ∈ B, a.gcd b ≤ (a / B.card : ℚ)) →
      ∃ a ∈ A, ∃ b ∈ A, a.gcd b ≤ (a / A.card : ℚ)) := by
    intro A hA hne hprim
    obtain ⟨x, hx⟩ := hne
    have hx0 : x ≠ 0 := ne_of_mem_of_not_mem hx hA
    have hgdvd : ∀ a ∈ A, A.gcd id ∣ a := fun a ha => Finset.gcd_dvd (f := id) ha
    have hg0 : A.gcd id ≠ 0 := by
      intro h0
      have h1 := hgdvd x hx
      rw [h0] at h1
      exact hx0 (Nat.eq_zero_of_zero_dvd h1)
    have hgpos : 0 < A.gcd id := Nat.pos_of_ne_zero hg0
    have hB0 : 0 ∉ A.image (fun a => a / A.gcd id) := by
      intro h
      obtain ⟨a, ha, hag⟩ := Finset.mem_image.mp h
      have ha0 : a ≠ 0 := ne_of_mem_of_not_mem ha hA
      obtain ⟨k, hk⟩ := hgdvd a ha
      have hk0 : k = 0 := by
        have h2 : a / A.gcd id = k := by
          conv_lhs => rw [hk]
          exact Nat.mul_div_cancel_left _ hgpos
        rw [← h2]; exact hag
      exact ha0 (by rw [hk, hk0, mul_zero])
    have hcard : (A.image (fun a => a / A.gcd id)).card = A.card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      exact (Nat.div_left_inj (hgdvd a ha) (hgdvd b hb)).mp hab
    have hgcd : (A.image (fun a => a / A.gcd id)).gcd id = 1 := by
      rw [Finset.gcd_image]
      exact Finset.gcd_div_id_eq_one hx hx0
    obtain ⟨a', ha', b', hb', hab⟩ := hprim _ hB0 hcard hgcd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
    refine ⟨a, ha, b, hb, ?_⟩
    obtain ⟨k, hk⟩ := hgdvd a ha
    obtain ⟨l, hl⟩ := hgdvd b hb
    have e1 : a / A.gcd id = k := by
      conv_lhs => rw [hk]
      exact Nat.mul_div_cancel_left _ hgpos
    have e2 : b / A.gcd id = l := by
      conv_lhs => rw [hl]
      exact Nat.mul_div_cancel_left _ hgpos
    rw [hcard, e1, e2] at hab
    have e3 : a.gcd b = A.gcd id * k.gcd l := by
      conv_lhs => rw [hk, hl]
      exact Nat.gcd_mul_left _ _ _
    have e4 : (a : ℚ) = ((A.gcd id : ℕ) : ℚ) * k := by exact_mod_cast hk
    rw [e3, e4]
    push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hab (by positivity)

  refine ⟨{1}, hh1, hh2, by simp, by simp, by simp, ?_⟩
  intro a ha b hb
  rw [Finset.mem_singleton] at ha hb
  subst ha hb
  exact ⟨1, 1, by simp⟩
