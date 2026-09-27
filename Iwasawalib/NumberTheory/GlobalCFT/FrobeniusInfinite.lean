/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.GlobalCFT.FrobeniusTower
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Algebra.Algebra.Subalgebra.Directed

@[expose] public section

/-!
# The Frobenius of a possibly infinite unramified abelian extension

An Artin map `Cl(F) → Gal(K/F)` for an unramified abelian extension `K / F` of a number field
has to be defined for `K / F` **not known to be finite**, because finiteness is itself a
consequence of class field theory: it follows from the surjectivity of the Artin map
(`NumberField.finiteDimensional_of_surjective_artinMapOfReciprocal_candidate`) or from the upper
bound of the Hilbert class field theorem
(`NumberField.finiteDimensional_of_hilbertClassFieldUpperBound`).  So nothing may assume it
beforehand.  Mathlib's `arithFrobAt` needs a finite Galois group, so it cannot be used directly.
This file removes the finiteness hypothesis.

## The construction

`K` is the directed union of its finite Galois subextensions `E`
(`NumberField.iSup_finGalSubalgebra`), each of which is a number field, abelian and unramified
over `F`, so `NumberField.globalFrobAt F E p` is defined.  These are compatible with inclusions
(`NumberField.coe_globalFrobAt_inclusion`, from
`Iwasawalib/NumberTheory/GlobalCFT/FrobeniusTower.lean`), so `Subalgebra.iSupLift` glues them
into an `F`-algebra endomorphism `NumberField.globalFrobAlgHom` of `K`, which is bijective
because it is bijective on each `E` (`NumberField.bijective_globalFrobAlgHom`).

## Main statements

* `NumberField.frobAt : Gal(K/F)` — the Frobenius at `p`, for `K / F` unramified abelian of
  arbitrary degree.
* `NumberField.restrictNormalHom_frobAt` — it restricts to `globalFrobAt F E p` on every finite
  intermediate field `E`.  This is the sense in which it is *the* Frobenius: the value at
  `x : K` is computed inside a finite subextension containing `x`.
* `NumberField.frobAt_eq_globalFrobAt` — when `K` happens to be a number field, `frobAt` is the
  Frobenius of the finite theory, hence `arithFrobAt (𝓞 F) Gal(K/F) P.asIdeal` for any `P`
  above `p`.  Without this the infinite construction would be a different object.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped IsMulCommutative nonZeroDivisors

namespace NumberField

variable (F K : Type*) [Field F] [NumberField F] [Field K] [Algebra F K]
  [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]

variable {F K} in
/-- A finite intermediate field of an extension of a number field is a number field. -/
instance numberField_intermediateField (E : IntermediateField F K) [FiniteDimensional F E] :
    NumberField E :=
  haveI := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI := FiniteDimensional.trans ℚ F E
  ⟨⟩

variable {F K} in
/-- An intermediate field of an everywhere unramified extension is everywhere unramified. -/
instance isUnramifiedEverywhere_intermediateField (E : IntermediateField F K) :
    IsUnramifiedEverywhere F E :=
  IsUnramifiedEverywhere.tower_bot F E K

variable {F K} in
/-- **The Frobenius of a finite subextension is compatible with inclusions.** -/
theorem coe_globalFrobAt_inclusion (p : HeightOneSpectrum (𝓞 F))
    {E E' : IntermediateField F K} [FiniteDimensional F E] [FiniteDimensional F E']
    (h : E ≤ E') (x : E) :
    ((globalFrobAt F E' p (IntermediateField.inclusion h x) : E') : K)
      = ((globalFrobAt F E p x : E) : K) := by
  letI : Algebra E E' := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext; rfl
  have key := restrictNormalHom_globalFrobAt F E E' p
  have hx : ((AlgEquiv.restrictNormalHom E (globalFrobAt F E' p) x : E) : K)
      = ((globalFrobAt F E p x : E) : K) := by rw [key]
  rw [← hx]
  have h2 : algebraMap E E' (AlgEquiv.restrictNormalHom E (globalFrobAt F E' p) x)
      = globalFrobAt F E' p (IntermediateField.inclusion h x) :=
    AlgEquiv.restrictNormal_commutes (globalFrobAt F E' p) E x
  have h3 : ∀ y : E, ((algebraMap E E' y : E') : K) = (y : K) := fun y => rfl
  rw [← h3, h2]

/-! ### The Frobenius of a possibly infinite unramified abelian extension -/

/-- The finite Galois subextensions of `K / F`, as a family of `F`-subalgebras of `K`. -/
def finGalSubalgebra : FiniteGaloisIntermediateField F K → Subalgebra F K :=
  fun E => E.toIntermediateField.toSubalgebra

theorem directed_finGalSubalgebra : Directed (· ≤ ·) (finGalSubalgebra F K) :=
  fun E E' => ⟨E ⊔ E',
    fun _ hx => le_sup_left (a := E.toIntermediateField) (b := E'.toIntermediateField) hx,
    fun _ hx => le_sup_right (a := E.toIntermediateField) (b := E'.toIntermediateField) hx⟩

omit [NumberField F] [IsUnramifiedEverywhere F K] in
theorem iSup_finGalSubalgebra : iSup (finGalSubalgebra F K) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  exact le_iSup (finGalSubalgebra F K) (FiniteGaloisIntermediateField.adjoin F {x})
    (FiniteGaloisIntermediateField.subset_adjoin F {x} (Set.mem_singleton x))

variable {F K} in
/-- The family of Frobenius maps of the finite Galois subextensions. -/
def finGalFrobFamily (p : HeightOneSpectrum (𝓞 F)) :
    ∀ E : FiniteGaloisIntermediateField F K, finGalSubalgebra F K E →ₐ[F] K :=
  fun E => (E.toIntermediateField.val).comp (globalFrobAt F E p).toAlgHom

variable {F K} in
theorem finGalFrobFamily_compatible (p : HeightOneSpectrum (𝓞 F))
    (E E' : FiniteGaloisIntermediateField F K) (h : finGalSubalgebra F K E ≤ finGalSubalgebra F K E') :
    finGalFrobFamily p E = (finGalFrobFamily p E').comp (Subalgebra.inclusion h) := by
  refine AlgHom.ext fun x => ?_
  exact (coe_globalFrobAt_inclusion p (E := E.toIntermediateField)
    (E' := E'.toIntermediateField) h x).symm

variable {F K} in
/-- **The Frobenius at `p` as an `F`-algebra endomorphism of `K`**, for a possibly infinite
unramified abelian extension `K / F`: on each finite Galois subextension `E` it is the
Frobenius `globalFrobAt F E p` of `E / F`. -/
def globalFrobAlgHom (p : HeightOneSpectrum (𝓞 F)) : K →ₐ[F] K :=
  (Subalgebra.iSupLift (finGalSubalgebra F K) (directed_finGalSubalgebra F K)
    (finGalFrobFamily p) (finGalFrobFamily_compatible p)
    ⊤ (iSup_finGalSubalgebra F K).ge).comp
    (Subalgebra.topEquiv (R := F) (A := K)).symm.toAlgHom

variable {F K} in
theorem globalFrobAlgHom_apply_of_mem (p : HeightOneSpectrum (𝓞 F))
    (E : FiniteGaloisIntermediateField F K) (x : K) (hx : x ∈ E.toIntermediateField) :
    globalFrobAlgHom p x = ((globalFrobAt F E p ⟨x, hx⟩ : E) : K) := by
  show Subalgebra.iSupLift (finGalSubalgebra F K) (directed_finGalSubalgebra F K)
    (finGalFrobFamily p) (finGalFrobFamily_compatible p) ⊤ (iSup_finGalSubalgebra F K).ge
    ((Subalgebra.topEquiv (R := F) (A := K)).symm x) = _
  exact Subalgebra.iSupLift_of_mem (K := finGalSubalgebra F K) (i := E)
    ((Subalgebra.topEquiv (R := F) (A := K)).symm x) hx

variable {F K} in
/-- **On every finite subextension the Frobenius endomorphism is the Frobenius of that
subextension.** -/
theorem globalFrobAlgHom_coe (p : HeightOneSpectrum (𝓞 F)) (E : IntermediateField F K)
    [FiniteDimensional F E] (x : E) :
    globalFrobAlgHom p (x : K) = ((globalFrobAt F E p x : E) : K) :=
  globalFrobAlgHom_apply_of_mem p ⟨E⟩ (x : K) x.2

variable {F K} in
theorem bijective_globalFrobAlgHom (p : HeightOneSpectrum (𝓞 F)) :
    Function.Bijective (globalFrobAlgHom (K := K) p) := by
  refine ⟨(globalFrobAlgHom (K := K) p).toRingHom.injective, fun y => ?_⟩
  obtain ⟨z, hz⟩ := (globalFrobAt F (FiniteGaloisIntermediateField.adjoin F {y}) p).surjective
    ⟨y, FiniteGaloisIntermediateField.subset_adjoin F {y} (Set.mem_singleton y)⟩
  refine ⟨(z : K), ?_⟩
  rw [globalFrobAlgHom_apply_of_mem p (FiniteGaloisIntermediateField.adjoin F {y}) (z : K) z.2]
  exact congrArg (fun w : (FiniteGaloisIntermediateField.adjoin F {y}).toIntermediateField => (w : K)) hz

variable {F K} in
/-- **The Frobenius at `p` of a possibly infinite unramified abelian extension `K / F`.** -/
def frobAt (p : HeightOneSpectrum (𝓞 F)) : Gal(K/F) :=
  AlgEquiv.ofBijective (globalFrobAlgHom p) (bijective_globalFrobAlgHom p)

variable {F K} in
@[simp]
theorem frobAt_apply (p : HeightOneSpectrum (𝓞 F)) (x : K) :
    frobAt p x = globalFrobAlgHom p x := rfl

variable {F K} in
/-- **The Frobenius of `K / F` restricts to the Frobenius of every finite subextension.** -/
theorem restrictNormalHom_frobAt (p : HeightOneSpectrum (𝓞 F))
    (E : IntermediateField F K) [FiniteDimensional F E] :
    AlgEquiv.restrictNormalHom E (frobAt (K := K) p) = globalFrobAt F E p := by
  refine AlgEquiv.ext fun x => ?_
  apply (algebraMap E K).injective
  show algebraMap E K (AlgEquiv.restrictNormal (frobAt (K := K) p) E x) = _
  rw [AlgEquiv.restrictNormal_commutes]
  exact globalFrobAlgHom_coe p E x

variable {F K} in
/-- **In the finite case the two constructions agree.** -/
theorem frobAt_eq_globalFrobAt [NumberField K] (p : HeightOneSpectrum (𝓞 F)) :
    frobAt (K := K) p = globalFrobAt F K p := by
  refine AlgEquiv.ext fun x => ?_
  have hx : x ∈ (⊤ : IntermediateField F K) := IntermediateField.mem_top
  have h1 := globalFrobAlgHom_coe p (⊤ : IntermediateField F K) ⟨x, hx⟩
  have h2 := restrictNormalHom_globalFrobAt F (⊤ : IntermediateField F K) K p
  show globalFrobAlgHom p x = _
  rw [h1, ← h2, AlgEquiv.restrictNormalHom_apply]

end NumberField
