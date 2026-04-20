/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Iwasawalib.NumberTheory.NumberField.HilbertClassField.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Frobenius

@[expose] public section

/-!

# Hilbert class field (experimental) - Artin map and class field theory

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace NumberField

/-! ### Artin map of an unramified abelian extension -/

namespace IsUnramifiedEverywhere

/-- If `K / F` is an unramified abelian extension of number fields,
then there is a natural map `Cl(F) → Gal(K/F)`
sending a prime ideal `p` to the Frobenius element `Frobₚ` in `Gal(K/F)`.
Its definition should not involve class field theory.
We omit its formal definition here, but use `sorry` instead.

NOTE: a priori we don't know `K / F` is finite, so for `x : K` the `Frobₚ x`
should be defined by the Frobenius on `F(x) / F` instead, which is a finite extension. -/
noncomputable def artinMap
    [NumberField F] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K] :
    ClassGroup (𝓞 F) →* Gal(K/F) := sorry

variable [NumberField F] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]

/-- The Artin map `p ↦ Frobₚ` is surjective. When `K / F` is finite, it could be proved by
Chebotarev density theorem. In general suppose there exists `σ : Gal(K/F)`
such that `Frobₚ ≠ σ` for all `p : Cl(K)`, then for each `p : Cl(K)` there is `x_p : K` such that
`Frobₚ x_p ≠ σ x_p`, hence the Artin map is not surjective on `F(x_p | p : Gal(K/F)) / F`,
which is a contradiction, since this is a finite extension. -/
theorem surjective_artinMap : Function.Surjective (artinMap F K) :=
  sorry

/-- An unramified abelian extension of a number field is a finite extension. -/
instance (priority := low) finiteDimensional : FiniteDimensional F K := by
  have := Finite.of_surjective _ (surjective_artinMap F K)
  exact IsGalois.finiteDimensional_of_finite F K

include F in
/-- An unramified abelian extension of a number field is a number field. -/
theorem numberField : NumberField K := by
  have := charZero_of_injective_algebraMap (algebraMap F K).injective
  have := FiniteDimensional.trans ℚ F K
  exact ⟨⟩

/-- The degree of an unramified abelian extension of a number field divides the class number of
the base field. -/
theorem finrank_dvd_classNumber : Module.finrank F K ∣ classNumber F := by
  rw [classNumber, Fintype.card_eq_nat_card, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_dvd_of_surjective _ (surjective_artinMap F K)

theorem artinMap_spec
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h : P.asIdeal.under (𝓞 F) = p.asIdeal) :
    haveI := numberField F K
    artinMap F K (.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩) =
      arithFrobAt (𝓞 F) Gal(K/F) P.asIdeal :=
  sorry

end IsUnramifiedEverywhere

/-! ### Maximal unramified abelian subextension -/

/-- The maximal unramified abelian subextension is a finite extension. -/
instance finiteDimensional_maximalUnramifiedAbelianExtension [NumberField F] :
    FiniteDimensional F (maximalUnramifiedAbelianExtension F K) :=
  IsUnramifiedEverywhere.finiteDimensional F _

instance numberField_maximalUnramifiedAbelianExtension [NumberField F] :
    NumberField (maximalUnramifiedAbelianExtension F K) :=
  IsUnramifiedEverywhere.numberField F _

/-! ### Hilbert class field -/

namespace IsUnramifiedEverywhere

/-- The Artin map `Cl(F) → Gal(H / F)` is bijective, if `H` is the maximal unramified abelian
subextension of `K / F` and `K` is separably closed. -/
theorem bijective_artinMap_of_isSepClosed [NumberField F] [IsSepClosed K] :
    Function.Bijective (artinMap F (maximalUnramifiedAbelianExtension F K)) :=
  sorry

/-- The natural isomorphism `Cl(F) ≃ Gal(H / F)` given by Artin map, where `H` is the maximal
unramified abelian subextension of `K / F` and `K` is separably closed. -/
noncomputable def artinEquivOfIsSepClosed [NumberField F] [IsSepClosed K] :
    ClassGroup (𝓞 F) ≃* Gal(maximalUnramifiedAbelianExtension F K/F) :=
  .ofBijective (artinMap F _) (bijective_artinMap_of_isSepClosed F K)

theorem artinEquivOfIsSepClosed_apply [NumberField F] [IsSepClosed K] (p) :
    artinEquivOfIsSepClosed F K p = artinMap F _ p := rfl

theorem finrank_eq_classNumber_of_isSepClosed [NumberField F] [IsSepClosed K] :
    Module.finrank F (maximalUnramifiedAbelianExtension F K) = classNumber F := by
  rw [classNumber, Fintype.card_eq_nat_card, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (artinEquivOfIsSepClosed F K).symm.toEquiv

/-- Any unramified abelian extension is a subfield of Hilbert class field. -/
noncomputable def liftOfIsSepClosed
    [NumberField F] [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (L : Type*) [Field L] [Algebra F L] [IsSepClosed L] :
    K →ₐ[F] maximalUnramifiedAbelianExtension F L :=
  sorry

end IsUnramifiedEverywhere

end NumberField
