/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section

/-!

# Supplementary results for abelian extension

-/

/-! ### Product of a family of group homomorphisms (should go mathlib) -/

/-- Combine a family of `MonoidHom`s `f_i : M →* N_i` into `M →* ∏ i, N i`
given by `x ↦ (i ↦ f_i x)`. -/
@[to_additive (attr := simps)
      /-- Combine a family of `AddMonoidHom`s `f_i : M →+ N_i` into `M →+ ∏ i, N i`
      given by `x ↦ (i ↦ f_i x)`. -/]
protected def MonoidHom.pi {M ι : Type*} {N : ι → Type*} [MulOneClass M] [∀ i, MulOneClass (N i)]
    (f : (i : ι) → (M →* N i)) : M →* ((i : ι) → N i) where
  toFun x i := f i x
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[to_additive]
theorem MonoidHom.ker_pi {M ι : Type*} {N : ι → Type*} [Group M] [∀ i, MulOneClass (N i)]
    (f : (i : ι) → (M →* N i)) : (MonoidHom.pi f).ker = ⨅ i, (f i).ker := by
  ext x
  simp [funext_iff (f := MonoidHom.pi f x)]

/-! ### The group homomorphism `Gal(⨆ i, E_i/F) → Π i, Gal(E_i/F)` -/

namespace IntermediateField

variable {F K ι : Type*} [Field F] [Field K] [Algebra F K] (E : (i : ι) → IntermediateField F K)

/-- TODO: go mathlib -/
theorem fixingSubgroup_iSup : (⨆ i, E i).fixingSubgroup = ⨅ i, (E i).fixingSubgroup := by
  ext
  simp [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]

section Normal

variable [∀ i, Normal F (E i)]

/-- The group homomorphism `Gal(K/F) → Π i, Gal(E_i/F)` for a family `E_i` of intermediate fields
of `K / F` which are normal over `F`. -/
noncomputable def piRestrictNormalHom : Gal(K/F) →* ((i : ι) → Gal(E i/F)) :=
  MonoidHom.pi fun i ↦ AlgEquiv.restrictNormalHom (E i)

theorem ker_piRestrictNormalHom : (piRestrictNormalHom E).ker = (⨆ i, E i).fixingSubgroup := by
  simp_rw [piRestrictNormalHom, MonoidHom.ker_pi, restrictNormalHom_ker, fixingSubgroup_iSup]

theorem injective_piRestrictNormalHom_of_iSup_eq_top (h : ⨆ i, E i = ⊤) :
    Function.Injective (piRestrictNormalHom E) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_piRestrictNormalHom, h, fixingSubgroup_top]

/-- The (injective) group homomorphism `Gal((⨆ i, E_i)/F) → Π i, Gal(E_i/F)` for a family `E_i` of
intermediate fields of `K / F` which are normal over `F`. -/
noncomputable def piRestrictNormalHom' :
    Gal((⨆ i, E i : IntermediateField F K)/F) →* ((i : ι) → Gal(E i/F)) :=
  haveI (i : ι) : Normal F (restrict (le_iSup E i)) :=
    Normal.of_algEquiv (restrict_algEquiv (le_iSup E i))
  letI f := piRestrictNormalHom fun i ↦ restrict (le_iSup E i)
  letI g := MulEquiv.piCongrRight fun i ↦ (restrict_algEquiv (le_iSup E i)).symm.autCongr
  MonoidHom.comp g f

theorem injective_piRestrictNormalHom' : Function.Injective (piRestrictNormalHom' E) := by
  have (i : ι) : Normal F (restrict (le_iSup E i)) :=
    Normal.of_algEquiv (restrict_algEquiv (le_iSup E i))
  simp only [piRestrictNormalHom', MonoidHom.coe_comp, MonoidHom.coe_coe, EquivLike.comp_injective]
  refine injective_piRestrictNormalHom_of_iSup_eq_top _ ?_
  apply_fun _ using lift_injective _
  simp only [lift_top, iSup_eq_adjoin, lift_adjoin, Set.image_iUnion]
  congr with i x
  have := le_iSup E i
  simpa [mem_restrict] using @this x

end Normal

/-! ### Compositum of abelian extensions is abelian -/

section IsAbelianGalois

instance isAbelianGalois_iSup [∀ i, IsAbelianGalois F (E i)] :
    IsAbelianGalois F (⨆ i, E i : IntermediateField F K) := by
  set L := ⨆ i, E i
  suffices IsMulCommutative Gal(L/F) by
    have : IsGalois F L := ⟨⟩
    exact ⟨⟩
  refine ⟨⟨fun x y ↦ ?_⟩⟩
  apply_fun _ using injective_piRestrictNormalHom' E
  simp_rw [map_mul]; exact mul_comm _ _

instance isAbelianGalois_sup (E1 E2 : IntermediateField F K) [IsAbelianGalois F E1]
    [IsAbelianGalois F E2] : IsAbelianGalois F (E1 ⊔ E2 : IntermediateField F K) := by
  let E : Fin 2 → _ := ![E1, E2]
  have : (i : Fin 2) → IsAbelianGalois F (E i)
    | 0 => inferInstanceAs (IsAbelianGalois F E1)
    | 1 => inferInstanceAs (IsAbelianGalois F E2)
  have : E1 ⊔ E2 = ⨆ i, E i := by apply le_antisymm <;> simp [le_iSup_iff, iSup_le_iff, E]
  convert isAbelianGalois_iSup E

end IsAbelianGalois

end IntermediateField
