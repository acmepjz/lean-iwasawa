module

public import Iwasawalib.NumberTheory.GlobalCFT.IdeleFrobenius
public import Mathlib.FieldTheory.Galois.GaloisClosure

@[expose] public section


noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped IsMulCommutative nonZeroDivisors

namespace NumberField

/-- The Frobenius homomorphism on fractional ideals is compatible with restriction to every
finite intermediate field. -/
theorem restrictNormalHom_frobIdealHom_candidate
    (F K : Type*) [Field F] [NumberField F] [Field K] [Algebra F K]
    [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (E : IntermediateField F K) [FiniteDimensional F E]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    AlgEquiv.restrictNormalHom E (frobIdealHom F K I) =
      frobIdealHom F E I := by
  classical
  let r : Gal(K/F) →* Gal(E/F) := AlgEquiv.restrictNormalHom (F := F) E
  change r (∏ᶠ p : HeightOneSpectrum (𝓞 F),
      frobAt (K := K) p ^ FractionalIdeal.count F p
        (I : FractionalIdeal (𝓞 F)⁰ F)) =
    ∏ᶠ p : HeightOneSpectrum (𝓞 F),
      frobAt (K := E) p ^ FractionalIdeal.count F p
        (I : FractionalIdeal (𝓞 F)⁰ F)
  rw [MonoidHom.map_finprod r (finite_mulSupport_frobAt_zpow F K
    (I : FractionalIdeal (𝓞 F)⁰ F))]
  apply finprod_congr
  intro p
  rw [map_zpow, restrictNormalHom_frobAt (K := K) p E]
  rw [frobAt_eq_globalFrobAt (F := F) (K := E) p]

/-- Artin reciprocity descends along a finite intermediate field. -/
theorem IsArtinReciprocal.intermediateField_candidate
    (F K : Type*) [Field F] [NumberField F] [Field K] [Algebra F K]
    [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (hK : IsArtinReciprocal F K)
    (E : IntermediateField F K) [FiniteDimensional F E] :
    IsArtinReciprocal F E := by
  intro x
  rw [← restrictNormalHom_frobIdealHom_candidate F K E, hK x, map_one]

/-- The conditional Artin map is natural under restriction to a finite intermediate field. -/
theorem restrictNormalHom_artinMapOfReciprocal_candidate
    (F K : Type*) [Field F] [NumberField F] [Field K] [Algebra F K]
    [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (hK : IsArtinReciprocal F K)
    (E : IntermediateField F K) [FiniteDimensional F E] :
    (AlgEquiv.restrictNormalHom E).comp (artinMapOfReciprocal F K hK) =
      artinMapOfReciprocal F E
        (IsArtinReciprocal.intermediateField_candidate F K hK E) := by
  apply MonoidHom.ext
  intro c
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [MonoidHom.comp_apply, artinMapOfReciprocal, MulEquiv.coe_toMonoidHom,
    ClassGroup.equiv_mk0, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  exact restrictNormalHom_frobIdealHom_candidate F K E (FractionalIdeal.mk0 F I)

/-- Reciprocity on every finite Galois intermediate field implies reciprocity for an
arbitrary Galois extension. -/
theorem isArtinReciprocal_of_finGal_candidate
    (F K : Type*) [Field F] [NumberField F] [Field K] [Algebra F K]
    [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (hfin : ∀ E : FiniteGaloisIntermediateField F K,
      IsArtinReciprocal F E) :
    IsArtinReciprocal F K := by
  intro x
  apply AlgEquiv.ext
  intro y
  let E := FiniteGaloisIntermediateField.adjoin F ({y} : Set K)
  have hy : y ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin F ({y} : Set K) (Set.mem_singleton y)
  have hr : AlgEquiv.restrictNormalHom E.toIntermediateField
      (frobIdealHom F K (toPrincipalIdeal (𝓞 F) F x)) = 1 := by
    rw [restrictNormalHom_frobIdealHom_candidate F K E.toIntermediateField, hfin E x]
  have hy' := congrArg (fun σ : Gal(E/F) => σ ⟨y, hy⟩) hr
  change _ = (⟨y, hy⟩ : E) at hy'
  change frobIdealHom F K (toPrincipalIdeal (𝓞 F) F x) y = y
  simpa only [AlgEquiv.restrictNormalHom_apply] using congrArg Subtype.val hy'

/-- A homomorphism from a finite group into an arbitrary Galois group is surjective when all
of its restrictions to finite Galois intermediate fields are surjective. -/
theorem surjective_of_surjective_restrictNormalHom_finGal_candidate
    {F K A : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K]
    [Group A] [Finite A]
    (φ : A →* Gal(K/F))
    (hφ : ∀ E : FiniteGaloisIntermediateField F K,
      Function.Surjective ((AlgEquiv.restrictNormalHom E).comp φ)) :
    Function.Surjective φ := by
  classical
  intro σ
  by_contra hσ
  have hne : ∀ a : A, φ a ≠ σ := by
    intro a ha
    exact hσ ⟨a, ha⟩
  have hex : ∀ a : A, ∃ x : K, φ a x ≠ σ x := by
    intro a
    by_contra h
    apply hne a
    apply AlgEquiv.ext
    intro z
    by_contra hz
    exact h ⟨z, hz⟩
  choose x hx using hex
  let E := FiniteGaloisIntermediateField.adjoin F (Set.range x)
  obtain ⟨a, ha⟩ := hφ E (AlgEquiv.restrictNormalHom E σ)
  have hxa : x a ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin F (Set.range x) ⟨a, rfl⟩
  have heq := congrArg (fun τ : Gal(E/F) => τ ⟨x a, hxa⟩) ha
  apply hx a
  simpa only [MonoidHom.comp_apply, AlgEquiv.restrictNormalHom_apply] using
    congrArg Subtype.val heq

/-- Finite-layer surjectivity of the compatible conditional Artin maps controls the Artin map
for an arbitrary unramified abelian extension. -/
theorem surjective_artinMapOfReciprocal_of_finGal_candidate
    (F K : Type*) [Field F] [NumberField F] [Field K] [Algebra F K]
    [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (hK : IsArtinReciprocal F K)
    (hfin : ∀ E : FiniteGaloisIntermediateField F K,
      Function.Surjective
        (artinMapOfReciprocal F E
          (IsArtinReciprocal.intermediateField_candidate F K hK E))) :
    Function.Surjective (artinMapOfReciprocal F K hK) := by
  apply surjective_of_surjective_restrictNormalHom_finGal_candidate
    (φ := artinMapOfReciprocal F K hK)
  intro E
  rw [restrictNormalHom_artinMapOfReciprocal_candidate F K hK E]
  exact hfin E

/-- Surjectivity of the idele Frobenius map transfers to the ideal Frobenius map. -/
theorem surjective_frobIdealHom_of_surjective_frobIdeleHom_candidate
    (F L : Type*) [Field F] [NumberField F] [Field L] [Algebra F L]
    [IsAbelianGalois F L] [IsUnramifiedEverywhere F L]
    (h : Function.Surjective (frobIdeleHom F L)) :
    Function.Surjective (frobIdealHom F L) := by
  rw [← MonoidHom.range_eq_top, range_frobIdealHom,
    ← range_frobIdeleHom, MonoidHom.range_eq_top]
  exact h

/-- A surjective conditional Artin map shows that `K / F` is finite, although `K` is not assumed
to be finite over `F`. -/
theorem finiteDimensional_of_surjective_artinMapOfReciprocal_candidate
    (F K : Type*) [Field F] [NumberField F] [Field K] [Algebra F K]
    [IsAbelianGalois F K] [IsUnramifiedEverywhere F K]
    (hrec : IsArtinReciprocal F K)
    (hsurj : Function.Surjective (artinMapOfReciprocal F K hrec)) :
    FiniteDimensional F K := by
  letI : Finite Gal(K/F) := Finite.of_surjective (artinMapOfReciprocal F K hrec) hsurj
  exact IsGalois.finiteDimensional_of_finite F K

end NumberField
