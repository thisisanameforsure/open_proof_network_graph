/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-! Digit $2$ in base $3$ representation of $2^n$ — imported from google-deepmind/formal-conjectures (FormalConjectures/Arxiv/2107.12475/CollatzLike.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it. Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

theorem Opn.CollatzLike (n : ℕ) (hn : 8 < n) :
    2 ∈ Nat.digits 3 (2^n) := by
  sorry
