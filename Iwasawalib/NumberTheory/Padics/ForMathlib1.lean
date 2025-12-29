/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-! ### Maybe these should be in mathlib -/

namespace PadicInt

open Function

theorem toZMod_surjective : Surjective (toZMod (p := p)) := fun x ↦ ⟨x.val, by simp⟩

theorem toZModPow_surjective : Surjective (toZModPow (p := p) n) := fun x ↦ ⟨x.val, by simp⟩

end PadicInt
