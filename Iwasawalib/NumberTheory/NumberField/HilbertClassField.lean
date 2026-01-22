/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Frobenius

@[expose] public section

/-!

# Hilbert class field (experimental)

-/

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace NumberField

/-! ### Assertion that a finite extension is unramified everywhere -/

/-- A typeclass asserting that a (potentially infinite) field extension `K / F` is unramified
everywhere. Defined to be that any finite subextension `E / F` is unramified at all finite places
and all infinite places. Only makes sense when the base field `F` is a number field. -/
@[mk_iff]
class IsUnramifiedEverywhere : Prop where
  isUnramifiedAt_of_heightOneSpectrum (E : IntermediateField F K) [FiniteDimensional F E]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal
  isUnramifiedAtInfinitePlaces (E : IntermediateField F K) [FiniteDimensional F E] :
    IsUnramifiedAtInfinitePlaces F E

theorem isUnramifiedEverywhere_iff_of_finiteDimensional [FiniteDimensional F K] :
    IsUnramifiedEverywhere F K ↔
      (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ∧
        IsUnramifiedAtInfinitePlaces F K := by
  sorry

/-- The maximal unramified abelian subextension of a number field `F` inside `K`. -/
def maximalUnramifiedAbelianExtension : IntermediateField F K :=
  sSup {E | IsAbelianGalois F E ∧ IsUnramifiedEverywhere F E}

/-- The maximal unramified abelian subextension is a finite extension.
A result in global class field theory. We cannot prove it here. -/
instance finiteDimensional_maximalUnramifiedAbelianExtension [NumberField F] :
    FiniteDimensional F (maximalUnramifiedAbelianExtension F K) := sorry

/-- The maximal unramified abelian subextension is an abelian extension.
Because compositum of abelian Galois extensions is also abelian.
Proof: the group homomorphism `Gal(⨆ i, E_i/F) → Π i, Gal(E_i/F)` is injective.
Should go mathlib. -/
instance isAbelianGalois_maximalUnramifiedAbelianExtension :
    IsAbelianGalois F (maximalUnramifiedAbelianExtension F K) := sorry

/-- The maximal unramified abelian subextension is unramified everywhere.
Because when considering only one place,
compositum of unramified extensions is also unramified.
Should find a proof and submit to mathlib. -/
instance isUnramifiedEverywhere_maximalUnramifiedAbelianExtension :
    IsUnramifiedEverywhere F (maximalUnramifiedAbelianExtension F K) := sorry

instance numberField_maximalUnramifiedAbelianExtension [NumberField F] :
    NumberField (maximalUnramifiedAbelianExtension F K) where
  to_finiteDimensional := FiniteDimensional.trans ℚ F _

namespace IsUnramifiedEverywhere

/-- An unramified everywhere abelian extension of a number field must be finite. -/
instance (priority := low) finiteDimensional
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    FiniteDimensional F K := sorry

/-- An unramified everywhere abelian extension of a number field must be a number field. -/
theorem numberField
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    NumberField K := by
  have := charZero_of_injective_algebraMap (algebraMap F K).injective
  have := FiniteDimensional.trans ℚ F K
  exact ⟨⟩

/-! ### Artin map of an unramified abelian extension -/

/-- If `K / F` is an unramified abelian extension, then there is a natural map `Cl(F) → Gal(K/F)`
sending a prime ideal `p` to the Frobenius element `Frobₚ` in `Gal(K/F)`.
We cannot give the formal definition of it here, but use `sorry` instead. -/
noncomputable def artinMap
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    ClassGroup (𝓞 F) →* Gal(K/F) := sorry

theorem artinMap_spec
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h : P.asIdeal.under (𝓞 F) = p.asIdeal) :
    haveI := numberField F K
    artinMap F K (.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩) =
      arithFrobAt (𝓞 F) Gal(K/F) P.asIdeal :=
  sorry

/-- The Artin map is `p ↦ Frobₚ` surjective. It is a consequence of a stronger result:
Chebotarev density theorem. -/
theorem surjective_artinMap
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    Function.Surjective (artinMap F K) :=
  sorry

end IsUnramifiedEverywhere

/-! ### Hilbert class field -/

/-- The Hilbert class field `H_F` of a number field `F`, defined as a `Type` corresponding to
the maximal unramified abelian extension of `F` inside its separable closure. -/
def HilbertClassField : Type _ := maximalUnramifiedAbelianExtension F (SeparableClosure F)

namespace HilbertClassField

noncomputable instance instField : Field (HilbertClassField F) :=
  inferInstanceAs (Field (maximalUnramifiedAbelianExtension ..))

noncomputable instance algebra : Algebra F (HilbertClassField F) :=
  inferInstanceAs (Algebra F (maximalUnramifiedAbelianExtension ..))

noncomputable instance instInhabited : Inhabited (HilbertClassField F) := ⟨0⟩

instance instCharZero [CharZero F] : CharZero (HilbertClassField F) :=
  charZero_of_injective_algebraMap (algebraMap F _).injective

instance instCharP (p : ℕ) [CharP F p] : CharP (HilbertClassField F) p :=
  charP_of_injective_algebraMap (algebraMap F _).injective p

instance instExpChar (p : ℕ) [ExpChar F p] : ExpChar (HilbertClassField F) p :=
  expChar_of_injective_algebraMap (algebraMap F _).injective p

noncomputable instance algebra' (R : Type*) [CommRing R] [Algebra R F] :
    Algebra R (HilbertClassField F) :=
  inferInstanceAs (Algebra R (maximalUnramifiedAbelianExtension ..))

instance instIsScalarTower (R : Type*) [CommRing R] [Algebra R F] :
    IsScalarTower R F (HilbertClassField F) :=
  inferInstanceAs (IsScalarTower R F (maximalUnramifiedAbelianExtension ..))

instance instNoZeroSMulDivisors (R : Type*) [CommRing R] [Algebra R F] [IsFractionRing R F] :
    NoZeroSMulDivisors R (HilbertClassField F) := by
  rw [NoZeroSMulDivisors.iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq R F (HilbertClassField F)]
  exact
    (Function.Injective.comp (FaithfulSMul.algebraMap_injective F (HilbertClassField F))
      (IsFractionRing.injective R F) :)

instance isSeparable : Algebra.IsSeparable F (HilbertClassField F) :=
  inferInstanceAs (Algebra.IsSeparable F (maximalUnramifiedAbelianExtension ..))

/-- The Hilbert class field `H_F` is a finite extension of `F`. -/
instance finiteDimensional [NumberField F] : FiniteDimensional F (HilbertClassField F) :=
  inferInstanceAs (FiniteDimensional F (maximalUnramifiedAbelianExtension ..))

/-- The Hilbert class field `H_F` is an abelian extension of `F`. -/
instance isAbelianGalois : IsAbelianGalois F (HilbertClassField F) :=
  inferInstanceAs (IsAbelianGalois F (maximalUnramifiedAbelianExtension ..))

/-- The Hilbert class field `H_F` is unramified everywhere over `F`. -/
instance isUnramifiedEverywhere : IsUnramifiedEverywhere F (HilbertClassField F) :=
  inferInstanceAs (IsUnramifiedEverywhere F (maximalUnramifiedAbelianExtension ..))

/-- The Hilbert class field `H_F` is a number field. -/
instance numberField [NumberField F] : NumberField (HilbertClassField F) :=
  inferInstanceAs (NumberField (maximalUnramifiedAbelianExtension ..))

/-- The Artin map `Cl(F) → Gal(H_F / F)` is bijective. -/
theorem bijective_artinMap [NumberField F] :
    Function.Bijective (IsUnramifiedEverywhere.artinMap F (HilbertClassField F)) :=
  sorry

/-- The natural isomorphism `Cl(F) ≃ Gal(H_F / F)` given by Artin map. -/
noncomputable def artinEquiv [NumberField F] :
    ClassGroup (𝓞 F) ≃* Gal(HilbertClassField F/F) :=
  .ofBijective (IsUnramifiedEverywhere.artinMap F _) (bijective_artinMap F)

theorem artinEquiv_apply [NumberField F] (p) :
    artinEquiv F p = IsUnramifiedEverywhere.artinMap F _ p := rfl

/-- Any unramified abelian extension is a subfield of Hilbert class field. -/
noncomputable def lift
    [NumberField F] [IsUnramifiedEverywhere F K] [IsAbelianGalois F K] :
    K →ₐ[F] HilbertClassField F :=
  sorry

end HilbertClassField

end NumberField
