/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.XinfFgTorsion

@[expose] public section

open IntermediateField Module NumberField PowerSeries
open scoped Pointwise commutatorElement

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable {H : MvZpExtension p ι K Kinf}

/-- S1: `Kinf Ln`, viewed directly inside `Linf` over the original base field `K`. -/
noncomputable def LnInK (n : ℕ) : IntermediateField K (H.Linf.restrictScalars K) :=
  (H.Ln'In n).restrictScalars K

private theorem restrictScalars_Ln'_eq_sup (n : ℕ) :
    (H.Ln' n).restrictScalars K =
      ((IsScalarTower.toAlgHom K Kinf (SeparableClosure Kinf)).fieldRange ⊔
        (H.Ln n).restrictScalars K) := by
  rw [Ln']
  apply le_antisymm
  · intro x hx
    exact IntermediateField.adjoin_induction Kinf
      (p := fun y _ ↦ y ∈
        (IsScalarTower.toAlgHom K Kinf (SeparableClosure Kinf)).fieldRange ⊔
          (H.Ln n).restrictScalars K)
      (fun y hy ↦ (show (H.Ln n).restrictScalars K ≤ _ from le_sup_right) hy)
      (fun y ↦ (show
        (IsScalarTower.toAlgHom K Kinf (SeparableClosure Kinf)).fieldRange ≤ _
          from le_sup_left) ⟨y, rfl⟩)
      (fun _ _ _ _ hx hy ↦ add_mem hx hy)
      (fun _ _ hx ↦ inv_mem hx)
      (fun _ _ _ _ hx hy ↦ mul_mem hx hy)
      hx
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact (IntermediateField.adjoin Kinf (H.Ln n : Set (SeparableClosure Kinf))).algebraMap_mem y
    · intro y hy
      exact IntermediateField.subset_adjoin Kinf (H.Ln n : Set (SeparableClosure Kinf)) hy

/-- S1: the layer `LnInK n` is Galois over `K`. -/
instance isGalois_K_LnInK (n : ℕ) : IsGalois K (H.LnInK n) := by
  let i : Kinf →ₐ[K] SeparableClosure Kinf := IsScalarTower.toAlgHom K Kinf _
  let Ekinf : IntermediateField K (SeparableClosure Kinf) := i.fieldRange
  haveI : IsGalois K Ekinf := by
    exact i.equivFieldRange.transfer_galois.1 inferInstance
  haveI : IsGalois K ((H.Ln n).restrictScalars K) := H.isGalois_K_restrictScalars_Ln n
  haveI : Normal K ↥(Ekinf ⊔ (H.Ln n).restrictScalars K) := inferInstance
  haveI : Algebra.IsSeparable K ↥(Ekinf ⊔ (H.Ln n).restrictScalars K) := inferInstance
  have hG : IsGalois K ↥((H.Ln' n).restrictScalars K) := by
    rw [H.restrictScalars_Ln'_eq_sup n]
    exact ⟨⟩
  unfold LnInK
  exact ((IntermediateField.restrict_algEquiv (H.Ln'_le_Linf n)).restrictScalars K).transfer_galois.1 hG

/-- S2: the fixing subgroup of `LnInK n`, restricted to `Xinf`, is exactly `YnIn n`. -/
theorem fixingSubgroup_LnInK_subgroupOf_Xinf_eq_YnIn (n : ℕ) :
    (H.LnInK n).fixingSubgroup.subgroupOf H.Xinf = H.YnIn n := by
  ext x
  rfl

set_option maxHeartbeats 2400000 in
/-- S3: `YnIn n` is invariant under the quotient conjugation action. -/
theorem conjAct_mem_YnIn
    (gamma : H.GG ⧸ H.Xinf) (n : ℕ) (x : H.Xinf)
    (hx : x ∈ H.YnIn n) :
    Subgroup.conjAct H.Xinf H.mul_comm_Xinf' gamma x ∈ H.YnIn n := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gamma
  rw [← H.fixingSubgroup_LnInK_subgroupOf_Xinf_eq_YnIn n] at hx ⊢
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [Subgroup.coe_conjAct_mk]
  exact Subgroup.Normal.conj_mem inferInstance _ hx _

set_option maxHeartbeats 2400000 in
/-- S3: the preceding conjugation invariance is exactly the required `X`-stability. -/
theorem X_smul_mem_YnIn
    (gamma : H.GG ⧸ H.Xinf) (n : ℕ)
    (x : Additive H.Xinf) (hx : x ∈ Subgroup.toAddSubgroup (H.YnIn n)) :
    letI := H.XinfLambdaModule gamma
    (PowerSeries.X : ℤ_[p]⟦X⟧) • x ∈ Subgroup.toAddSubgroup (H.YnIn n) := by
  letI := H.XinfLambdaModule gamma
  obtain ⟨y, rfl⟩ : ∃ y : H.Xinf, Additive.ofMul y = x := ⟨Additive.toMul x, rfl⟩
  rw [H.XinfLambdaModule_X_smul gamma y, Subgroup.ofMul_mem_toAddSubgroup]
  exact (H.YnIn n).mul_mem (H.conjAct_mem_YnIn gamma n y hx) ((H.YnIn n).inv_mem hx)

/-- S4: the honest `Lambda`-submodule whose carrier is `YnIn n`. -/
noncomputable def YnStableSubmodule
    (gamma : H.GG ⧸ H.Xinf) (n : ℕ) :
    letI := H.XinfLambdaModule gamma
    Submodule ℤ_[p]⟦X⟧ (Additive H.Xinf) := by
  letI := H.XinfLambdaModule gamma
  haveI := H.continuousSMul_XinfLambdaModule gamma
  exact IwasawaAlgebra.submoduleOfAddSubgroup (Subgroup.toAddSubgroup (H.YnIn n))
    (Subgroup.isClosed_toAddSubgroup (H.isClosed_YnIn n)) (H.X_smul_mem_YnIn gamma n)

/-- S4: restriction of `YnStableSubmodule` has exactly the established `Z_p` carrier. -/
theorem YnStableSubmodule_restrictScalars
    (gamma : H.GG ⧸ H.Xinf) (n : ℕ) :
    letI := H.XinfZpModule
    letI := H.XinfLambdaModule gamma
    haveI := H.isScalarTower_Xinf gamma
    (H.YnStableSubmodule gamma n).restrictScalars ℤ_[p] =
      H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n) := by
  letI := H.XinfZpModule
  letI := H.XinfLambdaModule gamma
  haveI := H.isScalarTower_Xinf gamma
  apply SetLike.coe_injective
  change ((Subgroup.toAddSubgroup (H.YnIn n) : AddSubgroup (Additive H.Xinf)) :
      Set (Additive H.Xinf)) =
    ((H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n) :
      Submodule ℤ_[p] (Additive H.Xinf)) : Set (Additive H.Xinf))
  exact (H.coe_xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n)).symm

end MvZpExtension
