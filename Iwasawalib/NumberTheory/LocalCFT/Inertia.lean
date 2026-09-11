/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.AdicResidueField
public import Iwasawalib.NumberTheory.LocalCFT.DecompositionAction
public import Iwasawalib.NumberTheory.CFT.LocalGalois

@[expose] public section

/-!
# Trivial inertia: the decomposition group acts faithfully on the residue field

At an unramified place `w | v` of a Galois extension of number fields the inertia group is
trivial, so the decomposition group `D_w` acts *faithfully* on the residue field.  Combined with
`Iwasawalib/NumberTheory/LocalCFT/AdicResidueField.lean`, which identifies the residue field of
`𝒪_w = w.adicCompletionIntegers L` with `𝓞_L ⧸ w`, this supplies the last hypothesis of the
cohomology computations in `Iwasawalib/NumberTheory/LocalCFT/Unramified.lean`.

The inertia group is computed by Mathlib: `Ideal.card_inertia_eq_ramificationIdxIn` says that
its order is the ramification index, and `Ideal.Quotient.map_ker_stabilizer_subtype` identifies
it with the kernel of the action of the decomposition group on `𝓞_L ⧸ w`.

## Main statements

* `NumberField.stabilizerHom_injective`: at an unramified place, `D_w → Aut(𝓞_L ⧸ w)` is
  injective.
* `NumberField.faithfulSMul_residueField`: at an unramified place, `D_w` acts faithfully on the
  residue field of `𝒪_w`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField IsLocalRing
open scoped Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- **Trivial inertia.**  At an unramified place the action of the decomposition group on the
residue field `𝓞_L ⧸ w` is faithful. -/
theorem stabilizerHom_injective (h : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    Function.Injective (Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal (L ≃ₐ[K] L)) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  have hcard : Nat.card (w.asIdeal.inertia (L ≃ₐ[K] L)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
      ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
    exact h
  rw [← MonoidHom.ker_eq_bot_iff]
  have hbot : w.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ := by rwa [← Subgroup.card_eq_one]
  have hmap := Ideal.Quotient.map_ker_stabilizer_subtype (P := w.asIdeal) (p := v.asIdeal)
    (G := L ≃ₐ[K] L)
  rw [hbot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 hmap

section Residue

attribute [local instance] IsLocalRing.residueMulSemiringAction

/-- The action of the decomposition group on `𝒪_w`, in the `adicCompletionIntegers` form. -/
@[instance_reducible] local instance decompositionAdicIntegersAction :
    MulSemiringAction (decompositionGroup K L w) (w.adicCompletionIntegers L) :=
  decompositionIntegersMulSemiringAction w

/-- The identification `𝓞_L ⧸ w ≃+* 𝒪_w / 𝔪_w` intertwines the two actions of the
decomposition group. -/
theorem quotientEquivResidueField_smul (d : decompositionGroup K L w) (a : 𝓞 L) :
    w.quotientEquivResidueField L (Ideal.Quotient.mk w.asIdeal ((d : L ≃ₐ[K] L) • a))
      = d • w.quotientEquivResidueField L (Ideal.Quotient.mk w.asIdeal a) := by
  rw [HeightOneSpectrum.quotientEquivResidueField_mk,
    HeightOneSpectrum.quotientEquivResidueField_mk,
    HeightOneSpectrum.residueFieldHom_apply, HeightOneSpectrum.residueFieldHom_apply,
    show d • residue (w.adicCompletionIntegers L)
        (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a)
      = residue (w.adicCompletionIntegers L)
        (d • algebraMap (𝓞 L) (w.adicCompletionIntegers L) a) from
      IsLocalRing.residueMap_residue d _]
  congr 1
  refine Subtype.ext ?_
  show ((algebraMap (𝓞 L) L ((d : L ≃ₐ[K] L) • a) : L) : w.adicCompletion L)
    = d • ((algebraMap (𝓞 L) L a : L) : w.adicCompletion L)
  rw [decomposition_smul_coe]
  have hco : (algebraMap (𝓞 L) L ((d : L ≃ₐ[K] L) • a))
      = (d : L ≃ₐ[K] L) (algebraMap (𝓞 L) L a) :=
    coe_smul_ringOfIntegers (d : L ≃ₐ[K] L) a
  exact congrArg (fun x : L ↦ ((x : w.adicCompletion L))) hco

/-- **The decomposition group acts faithfully on the residue field at an unramified place.**
This is the statement that the inertia group is trivial. -/
theorem faithfulSMul_residueField (h : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    FaithfulSMul (decompositionGroup K L w)
      (ResidueField (w.adicCompletionIntegers L)) := by
  refine ⟨fun {d₁ d₂} hd ↦ ?_⟩
  have hst : ∀ d : decompositionGroup K L w,
      (d : L ≃ₐ[K] L) ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := fun d ↦ by
    rw [← decompositionGroup_eq_stabilizer (K := K)]; exact d.2
  have key : Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal (L ≃ₐ[K] L) ⟨_, hst d₁⟩
      = Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal (L ≃ₐ[K] L) ⟨_, hst d₂⟩ := by
    refine AlgEquiv.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.stabilizerHom_apply, Ideal.Quotient.stabilizerHom_apply]
    apply (w.quotientEquivResidueField L).injective
    show w.quotientEquivResidueField L (Ideal.Quotient.mk w.asIdeal ((d₁ : L ≃ₐ[K] L) • a))
      = w.quotientEquivResidueField L (Ideal.Quotient.mk w.asIdeal ((d₂ : L ≃ₐ[K] L) • a))
    rw [quotientEquivResidueField_smul, quotientEquivResidueField_smul, hd]
  refine Subtype.ext ?_
  exact congrArg (fun x : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal ↦ (x : L ≃ₐ[K] L))
    (stabilizerHom_injective v w h key)

end Residue

section LocalCFTForm

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction

/-- The residue field of `𝒪_w`, in the form used by `LocalCFT`, is finite. -/
instance finite_residueField_integers :
    Finite (ResidueField (LocalCFT.integers (F := w.adicCompletion L))) :=
  inferInstanceAs (Finite (ResidueField (w.adicCompletionIntegers L)))

/-- **Faithfulness in the form used by `LocalCFT`.** -/
theorem faithfulSMul_residueField_integers (h : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    FaithfulSMul (decompositionGroup K L w)
      (ResidueField (LocalCFT.integers (F := w.adicCompletion L))) :=
  faithfulSMul_residueField v w h

end LocalCFTForm

end NumberField
