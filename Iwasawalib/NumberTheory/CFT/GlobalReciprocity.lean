/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.SplittingModule
public import Iwasawalib.NumberTheory.CFT.IdeleClassNormIndex

/-!
# The abstract global reciprocity map

This file states the general finite-group degree-zero Tate bridge and uses it to construct the
abstract global reciprocity map from a finite idele-class formation.  It deliberately contains
no Artin-symbol, Frobenius, or local-normalization assertion.
-/

@[expose] public noncomputable section

open CategoryTheory IsDedekindDomain groupCohomology
open scoped IsMulCommutative

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction
  CyclicTate.Additive.distribMulActionOfMulDistrib

namespace NumberField

variable (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

/-! ## The A1 datum consumed by A3 -/

/-- A global idele-class fundamental class together with the finite-class-formation axioms it
satisfies.  This structure contains no existence assertion and no local normalization. -/
structure IdeleClassFormationData [IsGalois F L] where
  fundamentalClass : groupCohomology (repIdeleClass F L) 2
  finiteClassFormation : Rep.split.FiniteClassFormation fundamentalClass

namespace IdeleClassGroup

variable [IsGalois F L]

/-! ## A2: the general degree-zero Tate bridge -/

/-- Base change of an idele class of `F`, regarded as a Galois-invariant idele class of `L`. -/
def baseChangeInvariant (c : Additive (IdeleClassGroup (𝓞 F) F)) :
    (repIdeleClass F L).ρ.invariants :=
  ⟨baseChangeAdd F L c, by
    intro sigma
    exact congrArg Additive.ofMul
      (galIdeleClassAut_baseChange sigma (Additive.toMul c))⟩

/-- The canonical class of an invariant element in categorical degree-zero Tate cohomology.
This is the quotient constructor transported through `TateCohomology.zeroIso`; it introduces no
second model of Tate cohomology. -/
def tateCohomologyZeroMk (x : (repIdeleClass F L).ρ.invariants) :
    tateCohomology (repIdeleClass F L) 0 :=
  (TateCohomology.zeroIso (repIdeleClass F L)).inv (QuotientAddGroup.mk x)

private def toTateCohomologyZero :
    Additive (IdeleClassGroup (𝓞 F) F) →+
      tateCohomology (repIdeleClass F L) 0 where
  toFun c := tateCohomologyZeroMk F L (baseChangeInvariant F L c)
  map_zero' := by
    unfold tateCohomologyZeroMk
    rw [show baseChangeInvariant F L 0 = 0 by
      apply Subtype.ext
      exact map_zero (baseChangeAdd F L)]
    rw [show QuotientAddGroup.mk (0 : (repIdeleClass F L).ρ.invariants) = 0 by rfl]
    exact map_zero _
  map_add' c d := by
    unfold tateCohomologyZeroMk
    rw [show baseChangeInvariant F L (c + d) =
      baseChangeInvariant F L c + baseChangeInvariant F L d by
        apply Subtype.ext
        exact map_add (baseChangeAdd F L) c d]
    rw [show QuotientAddGroup.mk
      (baseChangeInvariant F L c + baseChangeInvariant F L d) =
        QuotientAddGroup.mk (baseChangeInvariant F L c) +
          QuotientAddGroup.mk (baseChangeInvariant F L d) by rfl]
    exact map_add _ _ _

private theorem moduleIso_inv_eq_zero_iff {X Y : ModuleCat ℤ} (e : X ≅ Y) (y : Y) :
    e.inv y = 0 ↔ y = 0 := by
  constructor
  · intro h
    rw [← e.inv_hom_id_apply y, h, map_zero]
  · intro h
    rw [h, map_zero]

omit [IsGalois F L] in
private theorem tateCohomologyZeroMk_eq_zero_iff
    (x : (repIdeleClass F L).ρ.invariants) :
    tateCohomologyZeroMk F L x = 0 ↔
      (QuotientAddGroup.mk x :
        (repIdeleClass F L).ρ.invariants ⧸
          (LinearMap.range (repIdeleClass F L).ρ.norm).submoduleOf
            (repIdeleClass F L).ρ.invariants) = 0 := by
  let z : (repIdeleClass F L).ρ.invariants ⧸
      (LinearMap.range (repIdeleClass F L).ρ.norm).submoduleOf
        (repIdeleClass F L).ρ.invariants := QuotientAddGroup.mk x
  change (TateCohomology.zeroIso (repIdeleClass F L)).inv z = 0 ↔ z = 0
  exact moduleIso_inv_eq_zero_iff _ _

private theorem surjective_toTateCohomologyZero :
    Function.Surjective (toTateCohomologyZero F L) := by
  intro y
  let q : (repIdeleClass F L).ρ.invariants ⧸
      (LinearMap.range (repIdeleClass F L).ρ.norm).submoduleOf
        (repIdeleClass F L).ρ.invariants :=
    (TateCohomology.zeroIso (repIdeleClass F L)).hom y
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective _ q
  have hxrange : x.1 ∈ Set.range (baseChange F L) := by
    rw [range_baseChange_eq_setOf_fixed]
    intro sigma
    exact congrArg Additive.toMul (x.2 sigma)
  obtain ⟨c, hc⟩ := hxrange
  have hbc : baseChangeInvariant F L (Additive.ofMul c) = x := by
    apply Subtype.ext
    exact congrArg Additive.ofMul hc
  refine ⟨Additive.ofMul c, ?_⟩
  change (TateCohomology.zeroIso (repIdeleClass F L)).inv
    (QuotientAddGroup.mk (baseChangeInvariant F L (Additive.ofMul c))) = y
  rw [hbc]
  calc
    _ = (TateCohomology.zeroIso (repIdeleClass F L)).inv q :=
      congrArg (TateCohomology.zeroIso (repIdeleClass F L)).inv hx
    _ = y := by
      dsimp [q]
      exact (TateCohomology.zeroIso (repIdeleClass F L)).hom_inv_id_apply y

omit [IsGalois F L] in
private theorem toAdditive_repIdeleClass_norm
    (d : (repIdeleClass F L).V) :
    Rep.toAdditive (M := Gal(L/F)) (G := IdeleClassGroup (𝓞 L) L)
        ((repIdeleClass F L).ρ.norm d) =
      CyclicTate.normHom Gal(L/F) (Additive (IdeleClassGroup (𝓞 L) L))
        (Rep.toAdditive (M := Gal(L/F)) (G := IdeleClassGroup (𝓞 L) L) d) := by
  rw [CyclicTate.normHom_apply]
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rfl

omit [IsGalois F L] in
private theorem mem_repIdeleClass_norm_range_iff
    (c : Additive (IdeleClassGroup (𝓞 L) L)) :
    c ∈ LinearMap.range (repIdeleClass F L).ρ.norm ↔
      c ∈ CyclicTate.rangeNorm Gal(L/F) (Additive (IdeleClassGroup (𝓞 L) L)) := by
  constructor
  · rintro ⟨d, hd⟩
    rw [CyclicTate.mem_rangeNorm]
    refine ⟨Rep.toAdditive (M := Gal(L/F))
      (G := IdeleClassGroup (𝓞 L) L) d, ?_⟩
    rw [← toAdditive_repIdeleClass_norm]
    have hc : Rep.toAdditive (M := Gal(L/F)) (G := IdeleClassGroup (𝓞 L) L)
        (show (repIdeleClass F L).V from c) = c := rfl
    exact (congrArg (Rep.toAdditive (M := Gal(L/F))
      (G := IdeleClassGroup (𝓞 L) L)) hd).trans hc
  · rw [CyclicTate.mem_rangeNorm]
    rintro ⟨d, hd⟩
    refine ⟨(Rep.toAdditive (M := Gal(L/F))
      (G := IdeleClassGroup (𝓞 L) L)).symm d, ?_⟩
    apply (Rep.toAdditive (M := Gal(L/F))
      (G := IdeleClassGroup (𝓞 L) L)).injective
    rw [toAdditive_repIdeleClass_norm]
    rw [AddEquiv.apply_symm_apply]
    have hc : Rep.toAdditive (M := Gal(L/F)) (G := IdeleClassGroup (𝓞 L) L)
        (show (repIdeleClass F L).V from c) = c := rfl
    exact hd.trans hc.symm

omit [IsGalois F L] in
private theorem ker_toTateCohomologyZero :
    (toTateCohomologyZero F L).ker = normSubgroup F L := by
  ext c
  change tateCohomologyZeroMk F L (baseChangeInvariant F L c) = 0 ↔ _
  rw [tateCohomologyZeroMk_eq_zero_iff]
  rw [QuotientAddGroup.eq_zero_iff]
  change baseChangeAdd F L c ∈
    LinearMap.range (repIdeleClass F L).ρ.norm ↔ c ∈ normSubgroup F L
  rw [mem_repIdeleClass_norm_range_iff, normSubgroup, AddSubgroup.mem_comap]

/-- There is a unique additive equivalence from the idele-class norm quotient to categorical
degree-zero Tate cohomology that sends the class of `c` to the canonical Tate class of its base
change.  This is the general finite-group form of `C_F / N C_L = H-hat^0(G, C_L)`. -/
theorem existsUnique_quotientNormEquivTateCohomologyZero :
    ∃! e :
        (Additive (IdeleClassGroup (𝓞 F) F) ⧸ normSubgroup F L) ≃+
          tateCohomology (repIdeleClass F L) 0,
      ∀ c : Additive (IdeleClassGroup (𝓞 F) F),
        e (QuotientAddGroup.mk c) = tateCohomologyZeroMk F L (baseChangeInvariant F L c) := by
  let f := toTateCohomologyZero F L
  have hf_surj : Function.Surjective f := surjective_toTateCohomologyZero F L
  have hf_ker : f.ker = normSubgroup F L := ker_toTateCohomologyZero F L
  let e :
      (Additive (IdeleClassGroup (𝓞 F) F) ⧸ normSubgroup F L) ≃+
        tateCohomology (repIdeleClass F L) 0 :=
    (QuotientAddGroup.quotientAddEquivOfEq hf_ker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f hf_surj)
  refine ⟨e, ?_, ?_⟩
  · intro c
    rfl
  · intro e' he'
    ext q
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    exact (he' c).trans (by rfl)

/-- The canonical general finite-group identification
`C_F / N_{L/F} C_L ≃ H-hat^0(Gal(L/F), C_L)`. -/
def quotientNormEquivTateCohomologyZero :
    (Additive (IdeleClassGroup (𝓞 F) F) ⧸ normSubgroup F L) ≃+
      tateCohomology (repIdeleClass F L) 0 :=
  (existsUnique_quotientNormEquivTateCohomologyZero F L).choose

/-- The general Tate bridge sends a quotient class to the canonical degree-zero Tate class of
the corresponding invariant base-changed idele class. -/
@[simp] theorem quotientNormEquivTateCohomologyZero_mk
    (c : Additive (IdeleClassGroup (𝓞 F) F)) :
    quotientNormEquivTateCohomologyZero F L (QuotientAddGroup.mk c) =
      tateCohomologyZeroMk F L (baseChangeInvariant F L c) :=
  (existsUnique_quotientNormEquivTateCohomologyZero F L).choose_spec.1 c

end IdeleClassGroup

/-! ## A3: the abstract global reciprocity map -/

variable [IsAbelianGalois F L] [FiniteDimensional F L]

/-- The additive reciprocity equivalence obtained by composing the norm-quotient/Tate bridge,
Tate--Nakayama reciprocity for the chosen fundamental class, and the canonical identification of
an abelian Galois group with its abelianization. -/
def quotientNormEquivGalois (D : IdeleClassFormationData F L) :
    (Additive (IdeleClassGroup (𝓞 F) F) ⧸ IdeleClassGroup.normSubgroup F L) ≃+
      Additive Gal(L/F) := by
  letI : Rep.split.FiniteClassFormation D.fundamentalClass := D.finiteClassFormation
  exact
    (IdeleClassGroup.quotientNormEquivTateCohomologyZero F L).trans
      ((Rep.split.reciprocityIso (repIdeleClass F L) D.fundamentalClass).toLinearEquiv.toAddEquiv
        |>.trans (MulEquiv.toAdditive (Abelianization.equivOfComm (H := Gal(L/F))).symm))

/-- The canonical abstract global reciprocity homomorphism attached to the chosen idele-class
fundamental class.  The definition factors through `C_F / N C_L`, then uses
`Rep.split.reciprocityIso`; it is independent of the Frobenius-defined map. -/
def globalReciprocityMap (D : IdeleClassFormationData F L) :
    IdeleClassGroup (𝓞 F) F →* Gal(L/F) :=
  MonoidHom.toAdditive.symm
    ((quotientNormEquivGalois F L D).toAddMonoidHom.comp
      (QuotientAddGroup.mk' (IdeleClassGroup.normSubgroup F L)))

/-- The abstract global reciprocity map is surjective. -/
theorem surjective_globalReciprocityMap (D : IdeleClassFormationData F L) :
    Function.Surjective (globalReciprocityMap F L D) := by
  intro g
  obtain ⟨c, hc⟩ := (quotientNormEquivGalois F L D).surjective (Additive.ofMul g)
  obtain ⟨x, rfl⟩ :=
    QuotientAddGroup.mk'_surjective (IdeleClassGroup.normSubgroup F L) c
  exact ⟨Additive.toMul x, congrArg Additive.toMul hc⟩

end NumberField
