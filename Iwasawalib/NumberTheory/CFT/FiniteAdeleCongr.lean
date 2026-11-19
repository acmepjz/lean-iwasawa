/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup

public import Mathlib.RingTheory.Invariant.Basic

public import Iwasawalib.NumberTheory.CFT.HeightOneSpectrumCongr

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

/-! ## Functoriality of `congrRingHom`, and the induced isomorphism -/

namespace IsDedekindDomain.FiniteAdeleRing

section Functoriality

variable {A B C K L M : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B]
  [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
  [Field M] [Algebra C M] [IsFractionRing C M]

/-- `congrRingHom` is functorial: the map induced by a composite is the composite of the
induced maps.  The composite isomorphisms `e''`, `f''` are taken as arguments together with
the equations identifying them, so that the lemma can be applied with `e''` and `f''` in any
chosen normal form (for instance `RingEquiv.refl`). -/
theorem congrRingHom_comp (e : A ≃+* B) (f : K ≃+* L)
    (hef : ∀ a : A, f (algebraMap A K a) = algebraMap B L (e a))
    (e' : B ≃+* C) (f' : L ≃+* M)
    (hef' : ∀ b : B, f' (algebraMap B L b) = algebraMap C M (e' b))
    (e'' : A ≃+* C) (f'' : K ≃+* M)
    (hef'' : ∀ a : A, f'' (algebraMap A K a) = algebraMap C M (e'' a))
    (he : e.trans e' = e'') (hf : f.trans f' = f'') :
    (congrRingHom e' f' hef').comp (congrRingHom e f hef) = congrRingHom e'' f'' hef'' := by
  subst he
  subst hf
  refine RingHom.ext fun x ↦ FiniteAdeleRing.ext M fun u ↦ ?_
  rw [RingHom.comp_apply, congrRingHom_apply, congrRingHom_apply, congrRingHom_apply]
  refine (adicCompletionCongr_comp f f' _ _ u _ _
    (fun z ↦ (valuation_symm_equivOfRingEquiv e' f' hef' u (f z)).trans
      (valuation_symm_equivOfRingEquiv e f hef _ z)) _).trans ?_
  exact adicCompletionCongr_index_congr (equivOfRingEquiv_trans_symm_apply e e' u).symm u
    (f.trans f') _ _ (fun t ↦ x t)

/-- The map induced by the identity is the identity. -/
theorem congrRingHom_id (hef : ∀ a : A,
      (RingEquiv.refl K) (algebraMap A K a) = algebraMap A K ((RingEquiv.refl A) a)) :
    congrRingHom (RingEquiv.refl A) (RingEquiv.refl K) hef = RingHom.id (FiniteAdeleRing A K) := by
  refine RingHom.ext fun x ↦ FiniteAdeleRing.ext K fun v ↦ ?_
  rw [congrRingHom_apply, RingHom.id_apply]
  refine (adicCompletionCongr_index_congr (equivOfRingEquiv_refl_symm_apply v) v
    (RingEquiv.refl K) _ (fun _ ↦ rfl) (fun t ↦ x t)).trans ?_
  exact adicCompletionCongr_refl v _ (x v)

/-- A version of `congrRingHom_id` taking the equations to `RingEquiv.refl` as arguments. -/
theorem congrRingHom_eq_id (e : A ≃+* A) (f : K ≃+* K)
    (hef : ∀ a : A, f (algebraMap A K a) = algebraMap A K (e a))
    (he : e = RingEquiv.refl A) (hf : f = RingEquiv.refl K) :
    congrRingHom e f hef = RingHom.id (FiniteAdeleRing A K) := by
  subst he; subst hf; exact congrRingHom_id _

end Functoriality

section Equiv

variable {A B K L : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
  (e : A ≃+* B) (f : K ≃+* L)
  (hef : ∀ a : A, f (algebraMap A K a) = algebraMap B L (e a))

include hef

omit [IsDedekindDomain A] [IsDedekindDomain B] [IsFractionRing A K] [IsFractionRing B L] in
/-- The inverse pair of isomorphisms is compatible as well. -/
theorem congr_symm_compat :
    ∀ b : B, f.symm (algebraMap B L b) = algebraMap A K (e.symm b) := by
  intro b
  apply f.injective
  rw [RingEquiv.apply_symm_apply, hef, RingEquiv.apply_symm_apply]

/-- The ring **isomorphism** `𝔸_K^f ≃ 𝔸_L^f` induced by a compatible pair of isomorphisms
`e : A ≃+* B` and `f : K ≃+* L`. -/
def congrRingEquiv : FiniteAdeleRing A K ≃+* FiniteAdeleRing B L :=
  RingEquiv.ofRingHom (congrRingHom e f hef)
    (congrRingHom e.symm f.symm (congr_symm_compat e f hef))
    ((congrRingHom_comp e.symm f.symm (congr_symm_compat e f hef) e f hef
      (RingEquiv.refl B) (RingEquiv.refl L) (fun _ ↦ rfl)
      (RingEquiv.symm_trans_self e) (RingEquiv.symm_trans_self f)).trans (congrRingHom_id _))
    ((congrRingHom_comp e f hef e.symm f.symm (congr_symm_compat e f hef)
      (RingEquiv.refl A) (RingEquiv.refl K) (fun _ ↦ rfl)
      (RingEquiv.self_trans_symm e) (RingEquiv.self_trans_symm f)).trans (congrRingHom_id _))

@[simp]
theorem congrRingEquiv_apply (x : FiniteAdeleRing A K) :
    congrRingEquiv e f hef x = congrRingHom e f hef x := rfl

theorem coe_congrRingEquiv : ⇑(congrRingEquiv e f hef) = congrRingHom e f hef := rfl

@[simp]
theorem congrRingEquiv_symm_apply (y : FiniteAdeleRing B L) :
    (congrRingEquiv e f hef).symm y =
      congrRingHom e.symm f.symm (congr_symm_compat e f hef) y := rfl

theorem congrRingEquiv_algebraMap (k : K) :
    congrRingEquiv e f hef (algebraMap K (FiniteAdeleRing A K) k) =
      algebraMap L (FiniteAdeleRing B L) (f k) :=
  congrRingHom_algebraMap e f hef k

end Equiv

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

/-! ## The finite adeles as a Galois module -/

namespace NumberField.RingOfIntegers

variable {F₁ F₂ F₃ : Type*} [Field F₁] [Field F₂] [Field F₃]

@[simp]
theorem mapRingEquiv_refl : mapRingEquiv (RingEquiv.refl F₁) = RingEquiv.refl (𝓞 F₁) :=
  RingEquiv.ext fun _ ↦ ext rfl

theorem mapRingEquiv_trans (e : F₁ ≃+* F₂) (e' : F₂ ≃+* F₃) :
    mapRingEquiv (e.trans e') = (mapRingEquiv e).trans (mapRingEquiv e') :=
  RingEquiv.ext fun _ ↦ ext rfl

end NumberField.RingOfIntegers

namespace NumberField

open NumberField IsDedekindDomain

section Aut

variable {L : Type*} [Field L] [NumberField L]

/-- The automorphism of the finite adele ring of a number field `L` induced by a field
automorphism of `L`. -/
def finiteAdeleEquiv (σ : L ≃+* L) :
    FiniteAdeleRing (𝓞 L) L ≃+* FiniteAdeleRing (𝓞 L) L :=
  FiniteAdeleRing.congrRingEquiv (RingOfIntegers.mapRingEquiv σ) σ (mapRingEquiv_compat σ)

theorem coe_finiteAdeleEquiv (σ : L ≃+* L) : ⇑(finiteAdeleEquiv σ) = finiteAdeleMap σ := rfl

@[simp]
theorem finiteAdeleEquiv_apply (σ : L ≃+* L) (x : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleEquiv σ x = finiteAdeleMap σ x := rfl

@[simp]
theorem finiteAdeleEquiv_symm_apply (σ : L ≃+* L) (x : FiniteAdeleRing (𝓞 L) L) :
    (finiteAdeleEquiv σ).symm x = finiteAdeleMap σ.symm x := rfl

/-- The action of the group of ring automorphisms of `L` on the finite adele ring of `L`,
as a group homomorphism. -/
def finiteAdeleAutHom : RingAut L →* RingAut (FiniteAdeleRing (𝓞 L) L) where
  toFun := finiteAdeleEquiv
  map_one' := by
    refine RingEquiv.ext fun x ↦ ?_
    exact RingHom.congr_fun (FiniteAdeleRing.congrRingHom_eq_id
      (RingOfIntegers.mapRingEquiv (1 : RingAut L)) (1 : RingAut L)
      (mapRingEquiv_compat 1) RingOfIntegers.mapRingEquiv_refl rfl) x
  map_mul' σ τ := by
    refine RingEquiv.ext fun x ↦ ?_
    exact RingHom.congr_fun (FiniteAdeleRing.congrRingHom_comp
      (RingOfIntegers.mapRingEquiv τ) τ (mapRingEquiv_compat τ)
      (RingOfIntegers.mapRingEquiv σ) σ (mapRingEquiv_compat σ)
      (RingOfIntegers.mapRingEquiv (σ * τ)) (σ * τ) (mapRingEquiv_compat (σ * τ))
      (RingOfIntegers.mapRingEquiv_trans τ σ).symm rfl).symm x

@[simp]
theorem finiteAdeleAutHom_apply (σ : RingAut L) (x : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleAutHom σ x = finiteAdeleMap σ x := rfl

end Aut

section Galois

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- `AlgEquiv.toRingEquiv` as a group homomorphism. -/
def algEquivToRingAut : (L ≃ₐ[K] L) →* RingAut L where
  toFun := AlgEquiv.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The action of `Aut(L/K)` on the finite adele ring of `L`, as a group homomorphism into
the group of ring automorphisms.  For `L / K` Galois this is the action of `Gal(L/K)`
on `𝔸_L^f`. -/
def finiteAdeleAut : (L ≃ₐ[K] L) →* RingAut (FiniteAdeleRing (𝓞 L) L) :=
  finiteAdeleAutHom.comp (algEquivToRingAut K L)

@[simp]
theorem finiteAdeleAut_apply (σ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleAut K L σ x = finiteAdeleMap (σ : L ≃+* L) x := rfl

/-- The Galois action on the finite adele ring of a number field. -/
instance finiteAdeleMulSemiringAction :
    MulSemiringAction (L ≃ₐ[K] L) (FiniteAdeleRing (𝓞 L) L) :=
  MulSemiringAction.compHom _ (finiteAdeleAut K L)

variable {K L}

theorem finiteAdele_smul_def (σ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 L) L) :
    σ • x = finiteAdeleMap (σ : L ≃+* L) x := rfl

@[simp]
theorem finiteAdele_smul_apply (σ : L ≃ₐ[K] L) (x : FiniteAdeleRing (𝓞 L) L)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    (σ • x) w = IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr (σ : L ≃+* L) _ w
      (FiniteAdeleRing.valuation_symm_equivOfRingEquiv (RingOfIntegers.mapRingEquiv
        (σ : L ≃+* L)) (σ : L ≃+* L) (mapRingEquiv_compat _) w)
      (x ((IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
        (RingOfIntegers.mapRingEquiv (σ : L ≃+* L))).symm w)) := rfl

@[simp]
theorem finiteAdele_smul_algebraMap (σ : L ≃ₐ[K] L) (k : L) :
    σ • algebraMap L (FiniteAdeleRing (𝓞 L) L) k
      = algebraMap L (FiniteAdeleRing (𝓞 L) L) (σ k) :=
  finiteAdeleMap_algebraMap (σ : L ≃+* L) k

/-- The Galois action fixes the image of the base field `K` in the finite adeles of `L`. -/
@[simp]
theorem finiteAdele_smul_algebraMap_base (σ : L ≃ₐ[K] L) (k : K) :
    σ • algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L k)
      = algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L k) := by
  rw [finiteAdele_smul_algebraMap]
  congr 1
  exact σ.commutes k

end Galois

/-! ## The induced action on the finite ideles -/

section GaloisUnits

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The induced action of `Aut(L/K)` on the group of finite ideles of `L`, i.e. on the unit
group of the finite adele ring. -/
def finiteIdeleAut : (L ≃ₐ[K] L) →* MulAut ((FiniteAdeleRing (𝓞 L) L)ˣ) where
  toFun σ := Units.mapEquiv (finiteAdeleAut K L σ).toMulEquiv
  map_one' := by ext u; simp
  map_mul' σ τ := by ext u; simp

/-- The Galois action on the finite ideles. -/
instance finiteIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((FiniteAdeleRing (𝓞 L) L)ˣ) :=
  MulDistribMulAction.compHom _ (finiteIdeleAut K L)

variable {K L}

@[simp]
theorem finiteIdele_smul_coe (σ : L ≃ₐ[K] L) (u : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ((σ • u : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)
      = σ • (u : FiniteAdeleRing (𝓞 L) L) := rfl

theorem finiteIdele_smul_unitEmbedding (σ : L ≃ₐ[K] L) (x : Lˣ) :
    σ • FiniteAdeleRing.unitEmbedding (𝓞 L) L x
      = FiniteAdeleRing.unitEmbedding (𝓞 L) L
          (Units.mapEquiv (σ : L ≃ₐ[K] L).toRingEquiv.toMulEquiv x) := by
  refine Units.ext ?_
  rw [finiteIdele_smul_coe]
  show σ • algebraMap L (FiniteAdeleRing (𝓞 L) L) (x : L)
    = algebraMap L (FiniteAdeleRing (𝓞 L) L) (σ (x : L))
  rw [finiteAdele_smul_algebraMap]

/-- The Galois action on the finite ideles of `L` fixes the image of `Kˣ`. -/
theorem finiteIdele_smul_unitEmbedding_base (σ : L ≃ₐ[K] L) (x : Kˣ) :
    σ • FiniteAdeleRing.unitEmbedding (𝓞 L) L
        (Units.map (algebraMap K L : K →+* L).toMonoidHom x)
      = FiniteAdeleRing.unitEmbedding (𝓞 L) L
        (Units.map (algebraMap K L : K →+* L).toMonoidHom x) := by
  refine Units.ext ?_
  rw [finiteIdele_smul_coe]
  show σ • algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L (x : K))
    = algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L (x : K))
  rw [finiteAdele_smul_algebraMap_base]

end GaloisUnits

end NumberField

/-! ## The Galois action on the finite places, and the decomposition group -/

namespace NumberField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

section Places

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField L] in
theorem toRingAut_ringOfIntegers (σ : L ≃ₐ[K] L) :
    MulSemiringAction.toRingAut (L ≃ₐ[K] L) (𝓞 L) σ
      = RingOfIntegers.mapRingEquiv (σ : L ≃+* L) :=
  RingEquiv.ext fun _ ↦ RingOfIntegers.ext rfl

omit [NumberField L] in
/-- The Galois action on the finite places of `L` is given by `equivOfRingEquiv`. -/
theorem smul_heightOneSpectrum (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    σ • w = equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L)) w := by
  rw [HeightOneSpectrum.smul_def, toRingAut_ringOfIntegers]

omit [NumberField L] in
theorem inv_smul_heightOneSpectrum (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    σ⁻¹ • w = (equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L))).symm w := by
  rw [HeightOneSpectrum.inv_smul_eq_symm, toRingAut_ringOfIntegers]

/-- The valuation at `σ • w` of `σ x` is the valuation at `w` of `x`. -/
theorem valuation_smul_heightOneSpectrum (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    (σ • w).valuation L (σ x) = w.valuation L x := by
  rw [smul_heightOneSpectrum]
  exact valuation_equivOfRingEquiv (RingOfIntegers.mapRingEquiv (σ : L ≃+* L)) (σ : L ≃+* L)
    (mapRingEquiv_compat _) w x

/-- The `σ`-equivariant isomorphism between the completion at `w` and the completion
at `σ • w`. -/
def adicCompletionSmulEquiv (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    w.adicCompletion L ≃+* (σ • w).adicCompletion L :=
  adicCompletionCongr (σ : L ≃+* L) w (σ • w) (valuation_smul_heightOneSpectrum σ w)

@[simp]
theorem adicCompletionSmulEquiv_coe (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    adicCompletionSmulEquiv σ w (x : w.adicCompletion L)
      = ((σ x : L) : (σ • w).adicCompletion L) :=
  adicCompletionCongr_coe _ _ _ _ x

/-- The component of `σ • a` at `w` is obtained from the component of `a` at `σ⁻¹ • w`. -/
theorem finiteAdele_smul_apply_smul (σ : L ≃ₐ[K] L) (a : FiniteAdeleRing (𝓞 L) L)
    (w : HeightOneSpectrum (𝓞 L)) :
    (σ • a) (σ • w) = adicCompletionSmulEquiv σ w (a w) := by
  rw [finiteAdele_smul_apply]
  refine (adicCompletionCongr_index_congr ?_ (σ • w) (σ : L ≃+* L) _ _ (fun t ↦ a t)).symm
  rw [← inv_smul_heightOneSpectrum]
  exact (inv_smul_smul σ w).symm

end Places

/-! ## The places above a given place of the base field -/

section PlacesOver

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- `Gal(L/K)` commutes with the `𝓞 K`-algebra structure on `𝓞 L`. -/
instance : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm σ a b := by
    refine RingOfIntegers.ext ?_
    show σ (algebraMap K L (a : K) * (b : L)) = algebraMap K L (a : K) * σ (b : L)
    rw [map_mul, σ.commutes]

variable (K L)

/-- The set of finite places of `L` lying over a finite place `v` of `K`. -/
def placesOver (v : HeightOneSpectrum (𝓞 K)) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.under (𝓞 K) = v.asIdeal}

variable {K L}

omit [NumberField K] [NumberField L] in
theorem mem_placesOver {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOver K L v ↔ w.asIdeal.under (𝓞 K) = v.asIdeal := Iff.rfl

omit [NumberField K] [NumberField L] in
/-- The Galois action preserves the place of `K` lying under a place of `L`. -/
@[simp]
theorem under_smul_heightOneSpectrum (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal.under (𝓞 K) = w.asIdeal.under (𝓞 K) := by
  rw [HeightOneSpectrum.smul_asIdeal, Ideal.under_smul]

omit [NumberField K] [NumberField L] in
theorem smul_mem_placesOver {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ placesOver K L v) (σ : L ≃ₐ[K] L) : σ • w ∈ placesOver K L v := by
  rw [mem_placesOver, under_smul_heightOneSpectrum]
  exact hw

/-- `Gal(L/K)` acts transitively on the finite places of `L` above a finite place of `K`. -/
theorem exists_smul_eq_of_under_eq [IsGalois K L] (w w' : HeightOneSpectrum (𝓞 L))
    (h : w.asIdeal.under (𝓞 K) = w'.asIdeal.under (𝓞 K)) :
    ∃ σ : L ≃ₐ[K] L, σ • w = w' := by
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L)
    w.asIdeal w'.asIdeal h
  exact ⟨σ, HeightOneSpectrum.ext (by rw [HeightOneSpectrum.smul_asIdeal, ← hσ])⟩

/-- The orbit of a place `w` above `v` is exactly the set of places above `v`. -/
theorem orbit_eq_placesOver [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)}
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ placesOver K L v) :
    MulAction.orbit (L ≃ₐ[K] L) w = placesOver K L v := by
  refine Set.ext fun w' ↦ ⟨?_, ?_⟩
  · rintro ⟨σ, rfl⟩
    exact smul_mem_placesOver hw σ
  · intro hw'
    exact exists_smul_eq_of_under_eq w w' (hw.trans (mem_placesOver.1 hw').symm)

variable (K L)

/-- The decomposition group of a finite place `w` of `L`: the stabiliser of `w` in
`Gal(L/K)`. -/
def decompositionGroup (w : HeightOneSpectrum (𝓞 L)) : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer (L ≃ₐ[K] L) w

variable {K L}

omit [NumberField K] [NumberField L] in
theorem mem_decompositionGroup {w : HeightOneSpectrum (𝓞 L)} {σ : L ≃ₐ[K] L} :
    σ ∈ decompositionGroup K L w ↔ σ • w = w := Iff.rfl

/-- **Orbit-stabiliser for places**: the set of finite places of `L` above `v` is in
bijection with `Gal(L/K) ⧸ D_w`, where `D_w` is the decomposition group of any place `w`
above `v`.  This is the combinatorial input to Shapiro's lemma. -/
def placesOverEquivQuotientDecompositionGroup [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)}
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ placesOver K L v) :
    placesOver K L v ≃ (L ≃ₐ[K] L) ⧸ decompositionGroup K L w :=
  (Set.equivOfEq (orbit_eq_placesOver hw)).symm.trans
    (MulAction.orbitEquivQuotientStabilizer _ w)

omit [NumberField K] in
/-- An automorphism fixing the place `w` preserves the `w`-adic valuation. -/
theorem valuation_of_smul_eq {w : HeightOneSpectrum (𝓞 L)} {σ : L ≃ₐ[K] L} (hσ : σ • w = w)
    (x : L) : w.valuation L (σ x) = w.valuation L x := by
  conv_lhs => rw [← hσ]
  exact valuation_smul_heightOneSpectrum σ w x

omit [NumberField K] in
/-- An element of the decomposition group of `w` preserves the `w`-adic valuation. -/
theorem valuation_of_mem_decompositionGroup {w : HeightOneSpectrum (𝓞 L)}
    (d : decompositionGroup K L w) (x : L) :
    w.valuation L ((d : L ≃ₐ[K] L) x) = w.valuation L x :=
  valuation_of_smul_eq (mem_decompositionGroup.1 d.2) x

variable (K L)

omit [NumberField K] in
/-- The decomposition group of `w` acts on the local field `L_w`: this is the map
`D_w → Aut(L_w)` whose image is `Gal(L_w / K_v)` when `L / K` is Galois. -/
def decompositionRingAut (w : HeightOneSpectrum (𝓞 L)) :
    decompositionGroup K L w →* RingAut (w.adicCompletion L) where
  toFun d := adicCompletionCongr ((d : L ≃ₐ[K] L) : L ≃+* L) w w
    (valuation_of_mem_decompositionGroup d)
  map_one' := RingEquiv.ext fun z ↦ adicCompletionCongr_id _ w _ (fun _ ↦ rfl) z
  map_mul' d d' := RingEquiv.ext fun z ↦
    (adicCompletionCongr_comp ((d' : L ≃ₐ[K] L) : L ≃+* L) ((d : L ≃ₐ[K] L) : L ≃+* L)
      w w w (valuation_of_mem_decompositionGroup d') (valuation_of_mem_decompositionGroup d)
      (fun x ↦ (valuation_of_mem_decompositionGroup d _).trans
        (valuation_of_mem_decompositionGroup d' x)) z).symm

variable {K L}

omit [NumberField K] in
@[simp]
theorem decompositionRingAut_coe (w : HeightOneSpectrum (𝓞 L))
    (d : decompositionGroup K L w) (x : L) :
    decompositionRingAut K L w d (x : w.adicCompletion L)
      = (((d : L ≃ₐ[K] L) x : L) : w.adicCompletion L) :=
  adicCompletionCongr_coe _ w w (valuation_of_mem_decompositionGroup d) x

/-- The local Galois action of the decomposition group on the completion `L_w`. -/
instance decompositionMulSemiringAction (w : HeightOneSpectrum (𝓞 L)) :
    MulSemiringAction (decompositionGroup K L w) (w.adicCompletion L) :=
  MulSemiringAction.compHom _ (decompositionRingAut K L w)

omit [NumberField K] in
theorem decomposition_smul_def {w : HeightOneSpectrum (𝓞 L)} (d : decompositionGroup K L w)
    (z : w.adicCompletion L) : d • z = decompositionRingAut K L w d z := rfl

omit [NumberField K] in
@[simp]
theorem decomposition_smul_coe {w : HeightOneSpectrum (𝓞 L)} (d : decompositionGroup K L w)
    (x : L) : d • (x : w.adicCompletion L) = (((d : L ≃ₐ[K] L) x : L) : w.adicCompletion L) :=
  decompositionRingAut_coe w d x

omit [NumberField K] in
/-- The component at `w` of `d • a`, for `d` in the decomposition group of `w`, is the local
action of `d` on the component at `w` of `a`. -/
theorem finiteAdele_smul_apply_of_mem_decompositionGroup {w : HeightOneSpectrum (𝓞 L)}
    (d : decompositionGroup K L w) (a : FiniteAdeleRing (𝓞 L) L) :
    ((d : L ≃ₐ[K] L) • a) w = d • (a w) := by
  have hv : (equivOfRingEquiv
      (RingOfIntegers.mapRingEquiv ((d : L ≃ₐ[K] L) : L ≃+* L))).symm w = w := by
    rw [← inv_smul_heightOneSpectrum, inv_smul_eq_iff]
    exact (mem_decompositionGroup.1 d.2).symm
  rw [finiteAdele_smul_apply, decomposition_smul_def]
  exact adicCompletionCongr_index_congr hv w _ _
    (valuation_of_mem_decompositionGroup d) (fun t ↦ a t)

omit [NumberField K] in
theorem valuation_inv_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (y : L) :
    w.valuation L (σ y) = (σ⁻¹ • w).valuation L y := by
  conv_lhs => rw [← smul_inv_smul σ w]
  exact valuation_smul_heightOneSpectrum σ (σ⁻¹ • w) y

/-- The place `σ⁻¹ • w`, as a place above `v`. -/
def invSmulPlace {v : HeightOneSpectrum (𝓞 K)} (σ : L ≃ₐ[K] L) (w : placesOver K L v) :
    placesOver K L v :=
  ⟨σ⁻¹ • (w : HeightOneSpectrum (𝓞 L)), smul_mem_placesOver w.2 σ⁻¹⟩

omit [NumberField K] [NumberField L] in
@[simp]
theorem invSmulPlace_coe {v : HeightOneSpectrum (𝓞 K)} (σ : L ≃ₐ[K] L) (w : placesOver K L v) :
    (invSmulPlace σ w : HeightOneSpectrum (𝓞 L)) = σ⁻¹ • (w : HeightOneSpectrum (𝓞 L)) := rfl

variable (K L)

/-- The product `∏_{w ∣ v} L_w` of the completions of `L` at the finite places above a finite
place `v` of `K`. -/
abbrev LocalProduct (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  ∀ w : placesOver K L v, (w : HeightOneSpectrum (𝓞 L)).adicCompletion L

variable {K L}

/-- The Galois action on `∏_{w ∣ v} L_w`, permuting the factors and acting on each factor by
the induced isomorphism of completions. -/
instance localProductMulSemiringAction (v : HeightOneSpectrum (𝓞 K)) :
    MulSemiringAction (L ≃ₐ[K] L) (LocalProduct K L v) where
  smul σ x := fun w ↦ adicCompletionCongr ((σ : L ≃ₐ[K] L) : L ≃+* L)
    ((invSmulPlace σ w : HeightOneSpectrum (𝓞 L))) (w : HeightOneSpectrum (𝓞 L))
    (valuation_inv_smul σ _) (x (invSmulPlace σ w))
  one_smul x := funext fun w ↦ by
    refine (adicCompletionCongr_index_congr' Subtype.val
      (i' := w) (Subtype.ext (by simp)) (w : HeightOneSpectrum (𝓞 L)) _ _
      (fun _ ↦ rfl) x).trans ?_
    exact adicCompletionCongr_id _ _ _ (fun _ ↦ rfl) (x w)
  mul_smul σ τ x := funext fun w ↦ by
    refine (adicCompletionCongr_index_congr' Subtype.val
      (i' := invSmulPlace τ (invSmulPlace σ w))
      (Subtype.ext (by simp [mul_inv_rev, mul_smul])) (w : HeightOneSpectrum (𝓞 L)) _ _
      (fun y ↦ (valuation_inv_smul σ (w : HeightOneSpectrum (𝓞 L)) (τ y)).trans
        (valuation_inv_smul τ (σ⁻¹ • (w : HeightOneSpectrum (𝓞 L))) y)) x).trans ?_
    exact (adicCompletionCongr_comp _ _ _ _ _ (valuation_inv_smul τ _)
      (valuation_inv_smul σ _) _ _).symm
  smul_zero σ := funext fun w ↦ map_zero _
  smul_add σ x y := funext fun w ↦ map_add _ _ _
  smul_one σ := funext fun w ↦ map_one _
  smul_mul σ x y := funext fun w ↦ map_mul _ _ _

omit [NumberField K] in
theorem localProduct_smul_apply {v : HeightOneSpectrum (𝓞 K)} (σ : L ≃ₐ[K] L)
    (x : LocalProduct K L v) (w : placesOver K L v) :
    (σ • x) w = adicCompletionCongr ((σ : L ≃ₐ[K] L) : L ≃+* L)
      ((invSmulPlace σ w : HeightOneSpectrum (𝓞 L))) (w : HeightOneSpectrum (𝓞 L))
      (valuation_inv_smul σ _) (x (invSmulPlace σ w)) := rfl

end PlacesOver

/-! ## The induced-module description of `∏_{w ∣ v} L_w` -/

section Induced

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

omit [NumberField K] in
theorem valuation_smul_place (g : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (y : L) :
    w.valuation L ((g⁻¹ : L ≃ₐ[K] L) y) = (g • w).valuation L y := by
  conv_lhs => rw [← inv_smul_smul g w]
  exact valuation_smul_heightOneSpectrum g⁻¹ (g • w) y

omit [NumberField K] in
theorem valuation_of_smul_eq' {g : L ≃ₐ[K] L} {w w' : HeightOneSpectrum (𝓞 L)}
    (hg : g • w = w') (y : L) : w'.valuation L (g y) = w.valuation L y := by
  subst hg
  exact valuation_smul_heightOneSpectrum g w y

/-- The isomorphism `L_{g • w} ≃ L_w` induced by `g⁻¹`. -/
def adicCompletionPullback (g : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (g • w).adicCompletion L ≃+* w.adicCompletion L :=
  adicCompletionCongr ((g⁻¹ : L ≃ₐ[K] L) : L ≃+* L) (g • w) w (valuation_smul_place g w)

/-- The isomorphism `L_w ≃ L_{w'}` induced by an automorphism `g` carrying `w` to `w'`. -/
def adicCompletionPush {g : L ≃ₐ[K] L} {w w' : HeightOneSpectrum (𝓞 L)} (hg : g • w = w') :
    w.adicCompletion L ≃+* w'.adicCompletion L :=
  adicCompletionCongr ((g : L ≃ₐ[K] L) : L ≃+* L) w w' (valuation_of_smul_eq' hg)

variable (K L)

/-- The induced module `Ind_{D_w}^{Gal(L/K)} L_w`, realised as the subring of `D_w`-equivariant
functions `Gal(L/K) → L_w`. -/
def IndLocal (w : HeightOneSpectrum (𝓞 L)) :
    Subring ((L ≃ₐ[K] L) → w.adicCompletion L) where
  carrier := {F | ∀ (g : L ≃ₐ[K] L) (d : decompositionGroup K L w), F (g * d) = d⁻¹ • F g}
  one_mem' g d := by simp only [Pi.one_apply, smul_one]
  mul_mem' hF hF' g d := by
    simp only [Pi.mul_apply, hF g d, hF' g d, smul_mul']
  zero_mem' g d := by simp only [Pi.zero_apply, smul_zero]
  add_mem' hF hF' g d := by
    simp only [Pi.add_apply, hF g d, hF' g d, smul_add]
  neg_mem' hF g d := by
    simp only [Pi.neg_apply, hF g d, smul_neg]

variable {K L}

omit [NumberField K] in
theorem mem_indLocal {w : HeightOneSpectrum (𝓞 L)}
    {F : (L ≃ₐ[K] L) → w.adicCompletion L} :
    F ∈ IndLocal K L w ↔
      ∀ (g : L ≃ₐ[K] L) (d : decompositionGroup K L w), F (g * d) = d⁻¹ • F g := Iff.rfl

omit [NumberField K] in
@[simp]
theorem decompositionRingAut_apply (w : HeightOneSpectrum (𝓞 L))
    (d : decompositionGroup K L w) (z : w.adicCompletion L) :
    decompositionRingAut K L w d z =
      adicCompletionCongr ((d : L ≃ₐ[K] L) : L ≃+* L) w w
        (valuation_of_mem_decompositionGroup d) z := rfl

/-- Translation of a `D_w`-equivariant function by an element of `Gal(L/K)`. -/
def indLocalSmul {w : HeightOneSpectrum (𝓞 L)} (σ : L ≃ₐ[K] L) (F : IndLocal K L w) :
    IndLocal K L w :=
  ⟨fun g ↦ (F : (L ≃ₐ[K] L) → w.adicCompletion L) (σ⁻¹ * g), fun g d ↦ by
    show (F : (L ≃ₐ[K] L) → w.adicCompletion L) (σ⁻¹ * (g * (d : L ≃ₐ[K] L))) = _
    rw [← mul_assoc]
    exact F.2 (σ⁻¹ * g) d⟩

/-- The translation action of `Gal(L/K)` on the induced module. -/
instance indLocalMulSemiringAction (w : HeightOneSpectrum (𝓞 L)) :
    MulSemiringAction (L ≃ₐ[K] L) (IndLocal K L w) where
  smul := indLocalSmul
  one_smul F := Subtype.ext (funext fun g ↦ by
    show (F : (L ≃ₐ[K] L) → w.adicCompletion L) ((1 : L ≃ₐ[K] L)⁻¹ * g) = _
    rw [inv_one, one_mul])
  mul_smul σ τ F := Subtype.ext (funext fun g ↦ by
    show (F : (L ≃ₐ[K] L) → w.adicCompletion L) ((σ * τ)⁻¹ * g)
        = (F : (L ≃ₐ[K] L) → w.adicCompletion L) (τ⁻¹ * (σ⁻¹ * g))
    rw [mul_inv_rev, mul_assoc])
  smul_zero σ := Subtype.ext rfl
  smul_add σ F F' := Subtype.ext rfl
  smul_one σ := Subtype.ext rfl
  smul_mul σ F F' := Subtype.ext rfl

omit [NumberField K] in
@[simp]
theorem indLocal_smul_apply {w : HeightOneSpectrum (𝓞 L)} (σ : L ≃ₐ[K] L)
    (F : IndLocal K L w) (g : L ≃ₐ[K] L) :
    ((σ • F : IndLocal K L w) : (L ≃ₐ[K] L) → w.adicCompletion L) g =
      (F : (L ≃ₐ[K] L) → w.adicCompletion L) (σ⁻¹ * g) := rfl

variable {v : HeightOneSpectrum (𝓞 K)} {w₀ : HeightOneSpectrum (𝓞 L)}

/-- The underlying function of the map `∏_{w ∣ v} L_w → Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`. -/
def toIndLocalFun (hw₀ : w₀ ∈ placesOver K L v) (x : LocalProduct K L v) :
    (L ≃ₐ[K] L) → w₀.adicCompletion L :=
  fun g ↦ adicCompletionCongr ((g⁻¹ : L ≃ₐ[K] L) : L ≃+* L) (g • w₀) w₀
    (valuation_smul_place g w₀) (x ⟨g • w₀, smul_mem_placesOver hw₀ g⟩)

omit [NumberField K] in
theorem toIndLocalFun_apply (hw₀ : w₀ ∈ placesOver K L v) (x : LocalProduct K L v)
    (g : L ≃ₐ[K] L) :
    toIndLocalFun hw₀ x g = adicCompletionCongr ((g⁻¹ : L ≃ₐ[K] L) : L ≃+* L) (g • w₀) w₀
      (valuation_smul_place g w₀) (x ⟨g • w₀, smul_mem_placesOver hw₀ g⟩) := rfl

omit [NumberField K] in
theorem toIndLocalFun_mem (hw₀ : w₀ ∈ placesOver K L v) (x : LocalProduct K L v) :
    toIndLocalFun hw₀ x ∈ IndLocal K L w₀ := by
  intro g d
  rw [toIndLocalFun_apply, toIndLocalFun_apply, decomposition_smul_def,
    decompositionRingAut_apply]
  refine (adicCompletionCongr_index_congr' Subtype.val
    (i := (⟨(g * (d : L ≃ₐ[K] L)) • w₀,
      smul_mem_placesOver hw₀ (g * (d : L ≃ₐ[K] L))⟩ : placesOver K L v))
    (i' := (⟨g • w₀, smul_mem_placesOver hw₀ g⟩ : placesOver K L v))
    (Subtype.ext (show (g * (d : L ≃ₐ[K] L)) • w₀ = g • w₀ by
      rw [mul_smul, mem_decompositionGroup.1 d.2])) w₀ _ _ ?_ x).trans ?_
  · exact fun y ↦ (valuation_smul_place (g * (d : L ≃ₐ[K] L)) w₀ y).trans
      (by rw [mul_smul, mem_decompositionGroup.1 d.2])
  · refine (adicCompletionCongr_congr_equiv
      (f' := (((g⁻¹ : L ≃ₐ[K] L) : L ≃+* L).trans
        (((d⁻¹ : decompositionGroup K L w₀) : L ≃ₐ[K] L) : L ≃+* L)))
      (fun y ↦ rfl) (g • w₀) w₀ _ ?_ _).trans ?_
    · exact fun y ↦ (valuation_of_mem_decompositionGroup d⁻¹ _).trans
        (valuation_smul_place g w₀ y)
    · exact (adicCompletionCongr_comp _ _ (g • w₀) w₀ w₀ (valuation_smul_place g w₀)
        (valuation_of_mem_decompositionGroup d⁻¹) _ _).symm

/-- The ring homomorphism `∏_{w ∣ v} L_w → Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`. -/
def toIndLocal (hw₀ : w₀ ∈ placesOver K L v) :
    LocalProduct K L v →+* IndLocal K L w₀ where
  toFun x := ⟨toIndLocalFun hw₀ x, toIndLocalFun_mem hw₀ x⟩
  map_one' := Subtype.ext (funext fun _ ↦ map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ ↦ map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)

omit [NumberField K] in
@[simp]
theorem toIndLocal_coe (hw₀ : w₀ ∈ placesOver K L v) (x : LocalProduct K L v) :
    (toIndLocal hw₀ x : (L ≃ₐ[K] L) → w₀.adicCompletion L) = toIndLocalFun hw₀ x := rfl

omit [NumberField K] in
/-- `toIndLocal` is `Gal(L/K)`-equivariant. -/
theorem toIndLocal_smul (hw₀ : w₀ ∈ placesOver K L v) (σ : L ≃ₐ[K] L)
    (x : LocalProduct K L v) : toIndLocal hw₀ (σ • x) = σ • toIndLocal hw₀ x := by
  refine Subtype.ext (funext fun g ↦ ?_)
  rw [toIndLocal_coe, indLocal_smul_apply, toIndLocal_coe, toIndLocalFun_apply,
    toIndLocalFun_apply, localProduct_smul_apply]
  refine (adicCompletionCongr_comp _ _ _ (g • w₀) w₀ (valuation_inv_smul σ _)
    (valuation_smul_place g w₀) ?_ _).trans ?_
  · exact fun y ↦ (valuation_smul_place g w₀ _).trans (valuation_inv_smul σ _ y)
  refine (adicCompletionCongr_congr_equiv (f := (((σ : L ≃ₐ[K] L) : L ≃+* L).trans
      (((g⁻¹ : L ≃ₐ[K] L) : L ≃+* L))))
    (f' := (((σ⁻¹ * g)⁻¹ : L ≃ₐ[K] L) : L ≃+* L)) (fun y ↦ by
      show (g⁻¹ : L ≃ₐ[K] L) ((σ : L ≃ₐ[K] L) y) = ((σ⁻¹ * g)⁻¹ : L ≃ₐ[K] L) y
      rw [mul_inv_rev, inv_inv]
      rfl) _ w₀ _ ?_ _).trans ?_
  · exact fun y ↦ (valuation_smul_place (σ⁻¹ * g) w₀ y).trans
      (by rw [mul_smul]; rfl)
  · exact adicCompletionCongr_index_congr' Subtype.val
      (i := (invSmulPlace σ ⟨g • w₀, smul_mem_placesOver hw₀ g⟩))
      (i' := (⟨(σ⁻¹ * g) • w₀, smul_mem_placesOver hw₀ (σ⁻¹ * g)⟩ : placesOver K L v))
      (Subtype.ext (show σ⁻¹ • (g • w₀) = (σ⁻¹ * g) • w₀ from (mul_smul _ _ _).symm))
      w₀ _ _ _ x

/-! ### The inverse map -/

variable [IsGalois K L]

theorem exists_smul_eq_of_mem_placesOver (hw₀ : w₀ ∈ placesOver K L v)
    (w : placesOver K L v) : ∃ g : L ≃ₐ[K] L, g • w₀ = (w : HeightOneSpectrum (𝓞 L)) :=
  exists_smul_eq_of_under_eq w₀ (w : HeightOneSpectrum (𝓞 L))
    (hw₀.trans (mem_placesOver.1 w.2).symm)

/-- A choice of automorphism carrying the base place `w₀` to a given place above `v`. -/
noncomputable def placeWitness (hw₀ : w₀ ∈ placesOver K L v) (w : placesOver K L v) :
    L ≃ₐ[K] L :=
  (exists_smul_eq_of_mem_placesOver hw₀ w).choose

theorem placeWitness_spec (hw₀ : w₀ ∈ placesOver K L v) (w : placesOver K L v) :
    placeWitness hw₀ w • w₀ = (w : HeightOneSpectrum (𝓞 L)) :=
  (exists_smul_eq_of_mem_placesOver hw₀ w).choose_spec

omit [NumberField K] [IsGalois K L] in
/-- The value `g · F g` does not depend on the choice of `g` carrying `w₀` to `w`. -/
theorem indLocal_apply_congr (F : IndLocal K L w₀) {g g' : L ≃ₐ[K] L}
    {w : HeightOneSpectrum (𝓞 L)} (hg : g • w₀ = w) (hg' : g' • w₀ = w) :
    adicCompletionCongr ((g : L ≃ₐ[K] L) : L ≃+* L) w₀ w (valuation_of_smul_eq' hg)
        ((F : (L ≃ₐ[K] L) → w₀.adicCompletion L) g)
      = adicCompletionCongr ((g' : L ≃ₐ[K] L) : L ≃+* L) w₀ w (valuation_of_smul_eq' hg')
        ((F : (L ≃ₐ[K] L) → w₀.adicCompletion L) g') := by
  have hd : (g⁻¹ * g') • w₀ = w₀ := by
    rw [mul_smul, hg', ← hg, inv_smul_smul]
  set d : decompositionGroup K L w₀ := ⟨g⁻¹ * g', hd⟩ with hddef
  have hgd : g * (d : L ≃ₐ[K] L) = g' := by
    rw [hddef]
    show g * (g⁻¹ * g') = g'
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hF : (F : (L ≃ₐ[K] L) → w₀.adicCompletion L) g'
      = adicCompletionCongr (((d⁻¹ : decompositionGroup K L w₀) : L ≃ₐ[K] L) : L ≃+* L) w₀ w₀
        (valuation_of_mem_decompositionGroup d⁻¹)
        ((F : (L ≃ₐ[K] L) → w₀.adicCompletion L) g) := by
    conv_lhs => rw [← hgd]
    exact F.2 g d
  rw [hF]
  refine ((adicCompletionCongr_comp _ _ w₀ w₀ w (valuation_of_mem_decompositionGroup d⁻¹)
    (valuation_of_smul_eq' hg') ?_ _).trans ?_).symm
  · exact fun y ↦ (valuation_of_smul_eq' hg' _).trans
      (valuation_of_mem_decompositionGroup d⁻¹ y)
  · refine adicCompletionCongr_congr_equiv (fun y ↦ ?_) w₀ w _ _ _
    show (g' : L ≃ₐ[K] L) (((d⁻¹ : decompositionGroup K L w₀) : L ≃ₐ[K] L) y) = g y
    have : ((d⁻¹ : decompositionGroup K L w₀) : L ≃ₐ[K] L) = g'⁻¹ * g := by
      rw [hddef]
      show (g⁻¹ * g')⁻¹ = g'⁻¹ * g
      rw [mul_inv_rev, inv_inv]
    rw [this]
    show (g' : L ≃ₐ[K] L) ((g'⁻¹ * g : L ≃ₐ[K] L) y) = g y
    rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The inverse of `toIndLocal`, as a function. -/
noncomputable def ofIndLocalFun (hw₀ : w₀ ∈ placesOver K L v) (F : IndLocal K L w₀) :
    LocalProduct K L v :=
  fun w ↦ adicCompletionCongr ((placeWitness hw₀ w : L ≃ₐ[K] L) : L ≃+* L) w₀
    (w : HeightOneSpectrum (𝓞 L)) (valuation_of_smul_eq' (placeWitness_spec hw₀ w))
    ((F : (L ≃ₐ[K] L) → w₀.adicCompletion L) (placeWitness hw₀ w))

theorem ofIndLocalFun_apply (hw₀ : w₀ ∈ placesOver K L v) (F : IndLocal K L w₀)
    (w : placesOver K L v) {g : L ≃ₐ[K] L} (hg : g • w₀ = (w : HeightOneSpectrum (𝓞 L))) :
    ofIndLocalFun hw₀ F w = adicCompletionCongr ((g : L ≃ₐ[K] L) : L ≃+* L) w₀
      (w : HeightOneSpectrum (𝓞 L)) (valuation_of_smul_eq' hg)
      ((F : (L ≃ₐ[K] L) → w₀.adicCompletion L) g) :=
  indLocal_apply_congr F (placeWitness_spec hw₀ w) hg

theorem ofIndLocalFun_toIndLocal (hw₀ : w₀ ∈ placesOver K L v) (x : LocalProduct K L v) :
    ofIndLocalFun hw₀ (toIndLocal hw₀ x) = x := by
  funext w
  obtain ⟨w, hw⟩ := w
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_mem_placesOver hw₀ ⟨w, hw⟩
  rw [ofIndLocalFun_apply hw₀ _ _ (rfl : g • w₀ = g • w₀), toIndLocal_coe, toIndLocalFun_apply]
  refine (adicCompletionCongr_comp _ _ (g • w₀) w₀ (g • w₀)
    (valuation_smul_place g w₀) (valuation_of_smul_eq' rfl) ?_ _).trans ?_
  · exact fun y ↦ (valuation_of_smul_eq' (g := g) (w := w₀) rfl _).trans
      (valuation_smul_place g w₀ y)
  · exact adicCompletionCongr_id _ (g • w₀) _
      (fun y ↦ by
        show (g : L ≃ₐ[K] L) ((g⁻¹ : L ≃ₐ[K] L) y) = y
        rw [← AlgEquiv.mul_apply, mul_inv_cancel]
        rfl) _

theorem toIndLocal_ofIndLocalFun (hw₀ : w₀ ∈ placesOver K L v) (F : IndLocal K L w₀) :
    toIndLocal hw₀ (ofIndLocalFun hw₀ F) = F := by
  refine Subtype.ext (funext fun g ↦ ?_)
  rw [toIndLocal_coe, toIndLocalFun_apply,
    ofIndLocalFun_apply hw₀ F ⟨g • w₀, smul_mem_placesOver hw₀ g⟩ (rfl : g • w₀ = g • w₀)]
  refine (adicCompletionCongr_comp _ _ w₀ (g • w₀) w₀ (valuation_of_smul_eq' rfl)
    (valuation_smul_place g w₀) ?_ _).trans ?_
  · exact fun y ↦ (valuation_smul_place g w₀ _).trans
      (valuation_of_smul_eq' (g := g) (w := w₀) rfl y)
  · exact adicCompletionCongr_id _ w₀ _
      (fun y ↦ by
        show (g⁻¹ : L ≃ₐ[K] L) ((g : L ≃ₐ[K] L) y) = y
        rw [← AlgEquiv.mul_apply, inv_mul_cancel]
        rfl) _

/-- **The local factor of the finite adeles at `v` is an induced module.**  For a finite
Galois extension `L / K` of number fields, a finite place `v` of `K` and a place `w₀` of `L`
above `v`, the product `∏_{w ∣ v} L_w` is isomorphic, as a ring, to the induced module
`Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}` of `D_{w₀}`-equivariant functions `Gal(L/K) → L_{w₀}`.
The isomorphism is `Gal(L/K)`-equivariant by `localProductEquivIndLocal_smul`. -/
noncomputable def localProductEquivIndLocal (hw₀ : w₀ ∈ placesOver K L v) :
    LocalProduct K L v ≃+* IndLocal K L w₀ :=
  RingEquiv.ofBijective (toIndLocal hw₀)
    (Function.bijective_iff_has_inverse.2
      ⟨ofIndLocalFun hw₀, ofIndLocalFun_toIndLocal hw₀, toIndLocal_ofIndLocalFun hw₀⟩)

@[simp]
theorem localProductEquivIndLocal_apply (hw₀ : w₀ ∈ placesOver K L v)
    (x : LocalProduct K L v) : localProductEquivIndLocal hw₀ x = toIndLocal hw₀ x := rfl

@[simp]
theorem localProductEquivIndLocal_symm_apply (hw₀ : w₀ ∈ placesOver K L v)
    (F : IndLocal K L w₀) : (localProductEquivIndLocal hw₀).symm F = ofIndLocalFun hw₀ F := by
  rw [RingEquiv.symm_apply_eq, localProductEquivIndLocal_apply, toIndLocal_ofIndLocalFun]

/-- The induced-module isomorphism is `Gal(L/K)`-equivariant. -/
theorem localProductEquivIndLocal_smul (hw₀ : w₀ ∈ placesOver K L v) (σ : L ≃ₐ[K] L)
    (x : LocalProduct K L v) :
    localProductEquivIndLocal hw₀ (σ • x) = σ • localProductEquivIndLocal hw₀ x :=
  toIndLocal_smul hw₀ σ x

end Induced

end NumberField
