/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.UnitCohomology
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

@[expose] public section

/-!
# The action on the residue field of a local ring

A group acting on a local ring by ring automorphisms acts on its residue field: an automorphism
permutes the units, hence preserves the maximal ideal.  This file builds that induced action and
uses it to remove the residue field from the hypotheses of
`Iwasawalib/NumberTheory/LocalCFT/UnitCohomology.lean`: for a complete valued field `F` with a
`G`-fixed uniformizer, the canonical residue map `𝒪 → 𝒪/𝔪` satisfies `LocalCFT.IsLocalData`.

## Main definitions

* `IsLocalRing.residueMap`: the ring endomorphism of the residue field induced by `g : G`.
* `IsLocalRing.residueMulSemiringAction`: the induced `MulSemiringAction G (ResidueField R)`.

## Main statements

* `LocalCFT.isUnit_iff_valued_eq_one`: a valuation integer is a unit iff its valuation is `1`.
* `LocalCFT.isLocalData_residue`: the canonical residue map is local data.
-/

noncomputable section

open WithZero

namespace IsLocalRing

variable (G R : Type*) [Group G] [CommRing R] [IsLocalRing R] [MulSemiringAction G R]

variable {G R} in
theorem mem_maximalIdeal_smul_iff (g : G) (a : R) :
    g • a ∈ maximalIdeal R ↔ a ∈ maximalIdeal R := by
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    exact h (by simpa using hu.map (MulSemiringAction.toRingEquiv G R g).toRingHom)
  · intro h hu
    refine h ?_
    have := hu.map (MulSemiringAction.toRingEquiv G R g).symm.toRingHom
    simpa using this

variable {G R} in
/-- The endomorphism of the residue field induced by an element of `G`. -/
def residueMap (g : G) : ResidueField R →+* ResidueField R :=
  Ideal.Quotient.lift _ ((residue R).comp (MulSemiringAction.toRingEquiv G R g : R →+* R))
    fun a ha ↦ by
      rw [RingHom.comp_apply, residue_eq_zero_iff]
      exact (mem_maximalIdeal_smul_iff g a).2 ha

variable {G R} in
@[simp] theorem residueMap_residue (g : G) (a : R) :
    residueMap (R := R) g (residue R a) = residue R (g • a) := rfl

/-- **The induced action of `G` on the residue field of a local ring.** -/
@[instance_reducible] def residueMulSemiringAction :
    MulSemiringAction G (ResidueField R) where
  smul g x := residueMap g x
  one_smul x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show residueMap (1 : G) (residue R a) = residue R a
    rw [residueMap_residue, one_smul]
  mul_smul g h x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show residueMap (g * h) (residue R a) = residueMap g (residueMap h (residue R a))
    rw [residueMap_residue, residueMap_residue, residueMap_residue, mul_smul]
  smul_zero g := map_zero _
  smul_add g x y := map_add _ x y
  smul_one g := map_one _
  smul_mul g x y := map_mul _ x y

end IsLocalRing

namespace LocalCFT

open IsLocalRing

variable {F : Type*} [Field F] [hv : Valued F ℤᵐ⁰]

/-- **A valuation integer is a unit exactly when its valuation is one.** -/
theorem isUnit_iff_valued_eq_one (a : integers (F := F)) :
    IsUnit a ↔ Valued.v ((a : integers (F := F)) : F) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact valued_coe_units u
  · intro h
    exact ⟨unitOfValuedEqOne h, Subtype.ext rfl⟩

theorem residue_eq_zero_iff_valued_lt_one (a : integers (F := F)) :
    residue (integers (F := F)) a = 0 ↔ Valued.v ((a : integers (F := F)) : F) < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_valued_eq_one]
  exact ⟨fun h ↦ lt_of_le_of_ne a.2 h, fun h ↦ h.ne⟩

variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G (integers (F := F))]

attribute [local instance] residueMulSemiringAction

omit [Fintype G] in
/-- **The canonical residue map is local data.**  For a valued field whose valuation ring
carries a valuation-preserving `G`-action with a `G`-fixed uniformizer `π`, the reduction map
`𝒪 → 𝒪/𝔪` satisfies the hypotheses of `LocalCFT.IsLocalData`. -/
theorem isLocalData_residue
    (hG : ∀ (g : G) (a : integers (F := F)),
      Valued.v ((g • a : integers (F := F)) : F) = Valued.v ((a : integers (F := F)) : F))
    (π : integers (F := F)) (hπ : Valued.v ((π : integers (F := F)) : F) = exp (-1 : ℤ))
    (hπG : ∀ g : G, g • π = π) :
    IsLocalData (G := G) (residue (integers (F := F))) π where
  valued_smul := hG
  res_surjective := Ideal.Quotient.mk_surjective
  res_eq_zero_iff := residue_eq_zero_iff_valued_lt_one
  res_smul _ _ := rfl
  valued_uniformizer := hπ
  smul_uniformizer := hπG

end LocalCFT
