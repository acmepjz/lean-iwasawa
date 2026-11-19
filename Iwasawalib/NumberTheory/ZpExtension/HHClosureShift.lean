/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.L0Maximal
public import Iwasawalib.NumberTheory.ZpExtension.XnIsomQuot

@[expose] public section

open IntermediateField NumberField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

theorem topologicalClosure_HH_eq_fixingSubgroup_LinfFixedHH :
    H.HH.topologicalClosure = H.LinfFixedHH.fixingSubgroup := by
  have hle : H.HH.topologicalClosure ≤ H.LinfFixedHH.fixingSubgroup :=
    closure_minimal H.HH_le_fixingSubgroup_LinfFixedHH
      (InfiniteGalois.fixingSubgroup_isClosed H.LinfFixedHH)
  have hfields : IntermediateField.fixedField H.HH.topologicalClosure = H.LinfFixedHH :=
    le_antisymm (IntermediateField.fixedField_le (Subgroup.le_topologicalClosure H.HH))
      ((IntermediateField.le_iff_le (H := H.HH.topologicalClosure)
        (K := H.LinfFixedHH)).2 hle)
  have hclosed := InfiniteGalois.fixingSubgroup_fixedField
    (⟨H.HH.topologicalClosure, isClosed_closure⟩ : ClosedSubgroup H.GG)
  rw [hfields] at hclosed
  exact hclosed.symm

theorem fixingSubgroup_LinfFixedHH_subgroupOf_Xinf_eq_YnIn_zero :
    H.LinfFixedHH.fixingSubgroup.subgroupOf H.Xinf = H.YnIn 0 := by
  rw [← H.fixingSubgroup_L0In_eq]
  ext σ
  rw [Subgroup.mem_subgroupOf, H.mem_YnIn_iff, H.mem_Yn_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hfix x hx
    have hx' : (x : SeparableClosure Kinf) ∈ H.Ln' 0 := (H.mem_Ln'In 0 x).1 hx
    change H.xinfHom σ x = x
    apply Subtype.ext
    exact IntermediateField.adjoin_induction Kinf
      (motive := fun y hy ↦
        (((H.xinfHom σ) ⟨y, H.Ln'_le_Linf 0 hy⟩ : ↑H.Linf) :
          SeparableClosure Kinf) = y)
      (fun y hy ↦ by
        have hyL : y ∈ H.Linf := H.Ln_subset_Linf 0 hy
        have hy0 : (⟨y, hyL⟩ : ↑(H.Linf.restrictScalars K)) ∈ H.L0In := by
          rw [L0In, IntermediateField.mem_restrict,
            IntermediateField.mem_restrictScalars]
          exact hy
        exact congrArg Subtype.val (hfix ⟨y, hyL⟩ hy0))
      (fun y ↦ by simp)
      (fun x y hx hy hxe hye ↦ by
        have hxL : x ∈ H.Linf := H.Ln'_le_Linf 0 (by simpa [Ln'] using hx)
        have hyL : y ∈ H.Linf := H.Ln'_le_Linf 0 (by simpa [Ln'] using hy)
        let xl : ↑H.Linf := ⟨x, hxL⟩
        let yl : ↑H.Linf := ⟨y, hyL⟩
        have hadd : (⟨x + y, H.Linf.add_mem hxL hyL⟩ : ↑H.Linf) = xl + yl :=
          Subtype.ext rfl
        rw [hadd, map_add]
        exact congrArg₂ (fun a b : SeparableClosure Kinf ↦ a + b)
          (by simpa [xl] using hxe) (by simpa [yl] using hye))
      (fun x hx hxe ↦ by
        have hxL : x ∈ H.Linf := H.Ln'_le_Linf 0 (by simpa [Ln'] using hx)
        let xl : ↑H.Linf := ⟨x, hxL⟩
        have hinv : (⟨x⁻¹, H.Linf.inv_mem hxL⟩ : ↑H.Linf) = xl⁻¹ := Subtype.ext rfl
        rw [hinv, map_inv₀]
        exact congrArg Inv.inv (by simpa [xl] using hxe))
      (fun x y hx hy hxe hye ↦ by
        have hxL : x ∈ H.Linf := H.Ln'_le_Linf 0 (by simpa [Ln'] using hx)
        have hyL : y ∈ H.Linf := H.Ln'_le_Linf 0 (by simpa [Ln'] using hy)
        let xl : ↑H.Linf := ⟨x, hxL⟩
        let yl : ↑H.Linf := ⟨y, hyL⟩
        have hmul : (⟨x * y, H.Linf.mul_mem hxL hyL⟩ : ↑H.Linf) = xl * yl :=
          Subtype.ext rfl
        rw [hmul, map_mul]
        exact congrArg₂ (fun a b : SeparableClosure Kinf ↦ a * b)
          (by simpa [xl] using hxe) (by simpa [yl] using hye))
      hx'
  · intro hfix x hx
    have hx0 : (x : SeparableClosure Kinf) ∈ H.Ln 0 := by
      rw [L0In, IntermediateField.mem_restrict,
        IntermediateField.mem_restrictScalars] at hx
      exact hx
    have hx' : (x : SeparableClosure Kinf) ∈ H.Ln' 0 := H.Ln_subset_Ln' 0 hx0
    let y : ↑H.Linf := ⟨x, H.Ln'_le_Linf 0 hx'⟩
    have hy : y ∈ H.Ln'In 0 := (H.mem_Ln'In 0 y).2 hx'
    apply Subtype.ext
    exact congrArg Subtype.val (hfix y hy)

theorem topologicalClosure_HH_subgroupOf_Xinf_eq_YnIn_zero :
    H.HH.topologicalClosure.subgroupOf H.Xinf = H.YnIn 0 := by
  rw [H.topologicalClosure_HH_eq_fixingSubgroup_LinfFixedHH,
    H.fixingSubgroup_LinfFixedHH_subgroupOf_Xinf_eq_YnIn_zero]

theorem topologicalClosure_HH_shift_subgroupOf_Xinf_eq_YnIn_zero (n : ℕ) :
    (H.shift n).HH.topologicalClosure.subgroupOf (H.shift n).Xinf =
      (H.shift n).YnIn 0 :=
  (H.shift n).topologicalClosure_HH_subgroupOf_Xinf_eq_YnIn_zero

theorem map_topologicalClosure_HH_shift_eq_YnIn (n : ℕ) :
    Subgroup.map (H.xinfShiftMulEquiv n).toMonoidHom
      ((H.shift n).HH.topologicalClosure.subgroupOf (H.shift n).Xinf) = H.YnIn n := by
  rw [H.topologicalClosure_HH_shift_subgroupOf_Xinf_eq_YnIn_zero,
    H.map_YnIn_xinfShiftMulEquiv]

end MvZpExtension
