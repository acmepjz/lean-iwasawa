/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.AdicCompletionCongr

@[expose] public section

/-!
# Functoriality of the finite adele ring under isomorphisms

If `e : A ≃+* B` is an isomorphism of Dedekind domains and `f : K ≃+* L` is a compatible
isomorphism of their fraction fields, then `f` induces a ring homomorphism
`FiniteAdeleRing A K →+* FiniteAdeleRing B L`, given at the place `w` of `B` by the
isomorphism of adic completions at the place `e⁻¹ w` of `A`.

Applied with `A = B = 𝓞 L` and `f` a field automorphism of a number field `L`, this is the
action of the automorphism on the finite adeles.
-/

noncomputable section

open Filter Set IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

namespace IsDedekindDomain.FiniteAdeleRing

variable {A B K L : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
  (e : A ≃+* B) (f : K ≃+* L)

variable (hef : ∀ a : A, f (algebraMap A K a) = algebraMap B L (e a))

include hef

/-- The place of `A` lying under a place `w` of `B`, along the isomorphism `e`. -/
theorem valuation_symm_equivOfRingEquiv (w : HeightOneSpectrum B) (x : K) :
    w.valuation L (f x) = ((equivOfRingEquiv e).symm w).valuation K x := by
  conv_lhs => rw [← (equivOfRingEquiv e).apply_symm_apply w]
  exact valuation_equivOfRingEquiv e f hef _ x

/-- The ring homomorphism `𝔸_K^f → 𝔸_L^f` induced by a compatible pair of isomorphisms
`e : A ≃+* B` and `f : K ≃+* L`. -/
def congrRingHom : FiniteAdeleRing A K →+* FiniteAdeleRing B L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum A ↦ v.adicCompletion K)
    (fun w : HeightOneSpectrum B ↦ w.adicCompletion L)
    (fun w ↦ (equivOfRingEquiv e).symm w)
    ((equivOfRingEquiv e).symm.injective.tendsto_cofinite)
    (fun w ↦ (adicCompletionCongr f _ w
      (valuation_symm_equivOfRingEquiv e f hef w) : _ ≃+* _).toRingHom)
    (Eventually.of_forall fun w ↦
      adicCompletionCongr_mapsTo_integers f _ w (valuation_symm_equivOfRingEquiv e f hef w))

@[simp]
theorem congrRingHom_apply (x : FiniteAdeleRing A K) (w : HeightOneSpectrum B) :
    congrRingHom e f hef x w =
      adicCompletionCongr f _ w (valuation_symm_equivOfRingEquiv e f hef w)
        (x ((equivOfRingEquiv e).symm w)) := rfl

theorem congrRingHom_injective : Function.Injective (congrRingHom e f hef) := by
  intro x y hxy
  refine FiniteAdeleRing.ext K fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, (equivOfRingEquiv e).symm w = v :=
    ⟨equivOfRingEquiv e v, (equivOfRingEquiv e).symm_apply_apply v⟩
  have := congrArg (fun z : FiniteAdeleRing B L ↦ z w) hxy
  simpa only [congrRingHom_apply, EmbeddingLike.apply_eq_iff_eq] using this

@[simp]
theorem congrRingHom_algebraMap (k : K) :
    congrRingHom e f hef (algebraMap K (FiniteAdeleRing A K) k) =
      algebraMap L (FiniteAdeleRing B L) (f k) := by
  refine FiniteAdeleRing.ext L fun w ↦ ?_
  rw [congrRingHom_apply]
  simp only [FiniteAdeleRing.algebraMap_apply]
  exact adicCompletionCongr_coe f _ w (valuation_symm_equivOfRingEquiv e f hef w) k

end IsDedekindDomain.FiniteAdeleRing

/-! ## The action of a field automorphism of a number field on its finite adeles -/

namespace NumberField

open NumberField IsDedekindDomain

variable {L : Type*} [Field L] [NumberField L]

omit [NumberField L] in
theorem mapRingEquiv_compat (σ : L ≃+* L) (a : 𝓞 L) :
    σ (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv σ a) :=
  (RingOfIntegers.mapRingEquiv_apply σ a).symm

/-- The map induced on the finite adele ring of a number field `L` by a field automorphism
of `L`.  If `L / K` is Galois this gives the action of `Gal(L/K)` on `𝔸_L^f` (via
`AlgEquiv.toRingEquiv`). -/
def finiteAdeleMap (σ : L ≃+* L) :
    FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L :=
  FiniteAdeleRing.congrRingHom (RingOfIntegers.mapRingEquiv σ) σ (mapRingEquiv_compat σ)

theorem finiteAdeleMap_injective (σ : L ≃+* L) : Function.Injective (finiteAdeleMap σ) :=
  FiniteAdeleRing.congrRingHom_injective _ _ _

@[simp]
theorem finiteAdeleMap_algebraMap (σ : L ≃+* L) (k : L) :
    finiteAdeleMap σ (algebraMap L (FiniteAdeleRing (𝓞 L) L) k) =
      algebraMap L (FiniteAdeleRing (𝓞 L) L) (σ k) :=
  FiniteAdeleRing.congrRingHom_algebraMap _ _ _ k

end NumberField
