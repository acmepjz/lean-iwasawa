/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Iwasawalib.NumberTheory.Padics.EquivMvZp
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!

# Structure of `ℤₚˣ`

-/

variable (p : ℕ) [Fact p.Prime] (n : ℕ) (x : ℤ_[p]ˣ)

namespace PadicInt

/-- The subgroup of torsion elements of `ℤₚˣ`. -/
noncomputable def torsionUnits : Subgroup ℤ_[p]ˣ := CommGroup.torsion ℤ_[p]ˣ

/-- The subgroup `1 + qℤₚ` of `ℤₚˣ` where `q = 4` if `p = 2`, `q = p` if `p ≠ 2`. -/
noncomputable def torsionFreeUnits : Subgroup ℤ_[p]ˣ :=
  (Units.map (PadicInt.toZModPow (if p = 2 then 2 else 1)).toMonoidHom).ker

theorem mem_torsionUnits_iff : x ∈ torsionUnits p ↔ ∃ n, 0 < n ∧ x ^ n = 1 := by
  simp only [torsionUnits, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]

theorem mem_torsionFreeUnits_iff :
    x ∈ torsionFreeUnits p ↔ (p ^ if p = 2 then 2 else 1 : ℤ_[p]) ∣ x - 1 := by
  sorry

theorem torsionUnits_eq_rootsOfUnity :
    torsionUnits p = rootsOfUnity (p ^ if p = 2 then 2 else 1) _ := by
  sorry

theorem card_torsionUnits :
    Nat.card (torsionUnits p) = Nat.totient (p ^ if p = 2 then 2 else 1) := by
  sorry

theorem hasEnoughRootsOfUnity_iff :
    HasEnoughRootsOfUnity ℤ_[p] n ↔ n ∣ p ^ if p = 2 then 2 else 1 := by
  sorry

theorem disjoint_torsionUnits_torsionFreeUnits :
    Disjoint (torsionUnits p) (torsionFreeUnits p) := by
  sorry

theorem torsionUnits_sup_torsionFreeUnits :
    torsionUnits p ⊔ torsionFreeUnits p = ⊤ := by
  sorry

end PadicInt
