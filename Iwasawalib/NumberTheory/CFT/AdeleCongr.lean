/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.FiniteAdeleCongr
public import Iwasawalib.NumberTheory.CFT.IdeleClassGroup
public import Iwasawalib.NumberTheory.CFT.InfiniteAdeleCongr

@[expose] public section

/-!
# The Galois action on the adele ring, the idele group and the idele class group

Combining `NumberField.infiniteAdeleMap` (the archimedean half, from
`Iwasawalib.NumberTheory.CFT.InfiniteAdeleCongr`) with `NumberField.finiteAdeleMap` (the
non-archimedean half, from `Iwasawalib.NumberTheory.CFT.FiniteAdeleCongr`), a field
automorphism `σ` of a number field `L` acts on the adele ring `𝔸_L`, and this action is
functorial.  Because the action is compatible with `algebraMap L 𝔸_L`, it restricts to the
idele group `𝕀_L = 𝔸_Lˣ` and descends to the idele class group `C_L = 𝕀_L / Lˣ`.

## Main definitions

* `NumberField.adeleMap σ` : the ring homomorphism of `𝔸_L` induced by `σ : L ≃+* L`.
* `NumberField.adeleRingAut σ`, `NumberField.adeleAut` : the same as a ring automorphism, and
  as a monoid homomorphism `RingAut L →* RingAut 𝔸_L`.  This gives a `MulSemiringAction` of
  `RingAut L` on `𝔸_L`.
* `NumberField.ideleAut : RingAut L →* MulAut (IdeleGroup (𝓞 L) L)`.
* `NumberField.ideleClassAut : RingAut L →* MulAut (IdeleClassGroup (𝓞 L) L)`.
* `NumberField.galAdeleAut`, `NumberField.galIdeleAut`, `NumberField.galIdeleClassAut` : the
  versions for `Gal(L/K) = L ≃ₐ[K] L`.

## Main results

* `NumberField.adeleMap_trans`, `NumberField.adeleMap_refl` : functoriality.
* `NumberField.adeleMap_algebraMap` : compatibility with `algebraMap L 𝔸_L`.
* `NumberField.adeleAut_algebraMap_of_algebraMap` : the image of the base field `K` inside
  `𝔸_L` is fixed by `Gal(L/K)`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr_trans`,
  `adicCompletionCongr_refl` : the functoriality of `adicCompletionCongr` that the finite half
  needs.  These are proved here rather than in `FiniteAdeleCongr.lean`.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/-! ## Functoriality of `adicCompletionCongr` -/

namespace IsDedekindDomain.HeightOneSpectrum

variable {A B C K L M : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [CommRing C] [IsDedekindDomain C]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
  [Field M] [Algebra C M] [IsFractionRing C M]

theorem adicCompletionCongr_trans (f : K ≃+* L) (g : L ≃+* M) (v : HeightOneSpectrum A)
    (w : HeightOneSpectrum B) (u : HeightOneSpectrum C)
    (hf : ∀ x : K, w.valuation L (f x) = v.valuation K x)
    (hg : ∀ x : L, u.valuation M (g x) = w.valuation L x)
    (hfg : ∀ x : K, u.valuation M (f.trans g x) = v.valuation K x) (x : v.adicCompletion K) :
    adicCompletionCongr g w u hg (adicCompletionCongr f v w hf x)
      = adicCompletionCongr (f.trans g) v u hfg x := by
  have := Continuous.ext_on (denseRange_algebraMap (K := K) (v := v))
    ((continuous_adicCompletionCongr g w u hg).comp (continuous_adicCompletionCongr f v w hf))
    (continuous_adicCompletionCongr (f.trans g) v u hfg) ?_
  · exact congrFun this x
  · rintro _ ⟨k, rfl⟩
    show adicCompletionCongr g w u hg (adicCompletionCongr f v w hf ((k : K) : v.adicCompletion K))
      = adicCompletionCongr (f.trans g) v u hfg ((k : K) : v.adicCompletion K)
    rw [adicCompletionCongr_coe, adicCompletionCongr_coe, adicCompletionCongr_coe]
    rfl

end IsDedekindDomain.HeightOneSpectrum

/-! ## Functoriality of the action on the finite adeles -/

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

theorem finiteAdeleMap_trans (σ τ : L ≃+* L) :
    (finiteAdeleMap τ).comp (finiteAdeleMap σ) = finiteAdeleMap (σ.trans τ) := by
  refine RingHom.ext fun x ↦ FiniteAdeleRing.ext L fun w ↦ ?_
  exact adicCompletionCongr_trans σ τ _ _ w
    (FiniteAdeleRing.valuation_symm_equivOfRingEquiv _ σ (mapRingEquiv_compat σ) _)
    (FiniteAdeleRing.valuation_symm_equivOfRingEquiv _ τ (mapRingEquiv_compat τ) w)
    (FiniteAdeleRing.valuation_symm_equivOfRingEquiv _ (σ.trans τ)
      (mapRingEquiv_compat (σ.trans τ)) w) _

theorem finiteAdeleMap_refl :
    finiteAdeleMap (RingEquiv.refl L) = RingHom.id (FiniteAdeleRing (𝓞 L) L) := by
  refine RingHom.ext fun x ↦ FiniteAdeleRing.ext L fun w ↦ ?_
  exact adicCompletionCongr_refl _
    (FiniteAdeleRing.valuation_symm_equivOfRingEquiv _ (RingEquiv.refl L)
      (mapRingEquiv_compat (RingEquiv.refl L)) w) _

end NumberField

/-! ## The adele ring as a product -/

namespace NumberField.AdeleRing

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The adele ring is by definition the product of the infinite and the finite adele rings. -/
def prodEquiv : AdeleRing R K ≃+* InfiniteAdeleRing K × FiniteAdeleRing R K := RingEquiv.refl _

@[simp]
theorem prodEquiv_algebraMap (x : K) :
    prodEquiv R K (algebraMap K (AdeleRing R K) x) =
      (algebraMap K (InfiniteAdeleRing K) x, algebraMap K (FiniteAdeleRing R K) x) := rfl

end NumberField.AdeleRing

/-! ## The action of a field automorphism on the adele ring -/

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- The ring homomorphism of the adele ring `𝔸_L` induced by a field automorphism
`σ : L ≃+* L`. -/
def adeleMap (σ : L ≃+* L) : AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L :=
  (AdeleRing.prodEquiv (𝓞 L) L).symm.toRingHom.comp
    (((infiniteAdeleMap σ).prodMap (finiteAdeleMap σ)).comp
      (AdeleRing.prodEquiv (𝓞 L) L).toRingHom)

@[simp]
theorem adeleMap_fst (σ : L ≃+* L) (x : AdeleRing (𝓞 L) L) :
    (AdeleRing.prodEquiv (𝓞 L) L (adeleMap σ x)).1 =
      infiniteAdeleMap σ (AdeleRing.prodEquiv (𝓞 L) L x).1 := rfl

@[simp]
theorem adeleMap_snd (σ : L ≃+* L) (x : AdeleRing (𝓞 L) L) :
    (AdeleRing.prodEquiv (𝓞 L) L (adeleMap σ x)).2 =
      finiteAdeleMap σ (AdeleRing.prodEquiv (𝓞 L) L x).2 := rfl

theorem adeleMap_ext {x y : AdeleRing (𝓞 L) L}
    (h₁ : (AdeleRing.prodEquiv (𝓞 L) L x).1 = (AdeleRing.prodEquiv (𝓞 L) L y).1)
    (h₂ : (AdeleRing.prodEquiv (𝓞 L) L x).2 = (AdeleRing.prodEquiv (𝓞 L) L y).2) : x = y :=
  (AdeleRing.prodEquiv (𝓞 L) L).injective (Prod.ext h₁ h₂)

@[simp]
theorem adeleMap_algebraMap (σ : L ≃+* L) (k : L) :
    adeleMap σ (algebraMap L (AdeleRing (𝓞 L) L) k) =
      algebraMap L (AdeleRing (𝓞 L) L) (σ k) :=
  adeleMap_ext (by simp) (by simp)

theorem adeleMap_trans (σ τ : L ≃+* L) :
    (adeleMap τ).comp (adeleMap σ) = adeleMap (σ.trans τ) := by
  refine RingHom.ext fun x ↦ adeleMap_ext ?_ ?_
  · exact DFunLike.congr_fun (infiniteAdeleMap_trans σ τ) _
  · exact DFunLike.congr_fun (finiteAdeleMap_trans σ τ) _

theorem adeleMap_refl : adeleMap (RingEquiv.refl L) = RingHom.id (AdeleRing (𝓞 L) L) := by
  refine RingHom.ext fun x ↦ adeleMap_ext ?_ ?_
  · exact DFunLike.congr_fun infiniteAdeleMap_refl _
  · exact DFunLike.congr_fun finiteAdeleMap_refl _

/-- The ring automorphism of the adele ring `𝔸_L` induced by `σ : L ≃+* L`. -/
def adeleRingAut (σ : L ≃+* L) : RingAut (AdeleRing (𝓞 L) L) :=
  RingEquiv.ofRingHom (adeleMap σ) (adeleMap σ.symm)
    (by rw [adeleMap_trans, RingEquiv.symm_trans_self, adeleMap_refl])
    (by rw [adeleMap_trans, RingEquiv.self_trans_symm, adeleMap_refl])

@[simp]
theorem adeleRingAut_apply (σ : L ≃+* L) (x : AdeleRing (𝓞 L) L) :
    adeleRingAut σ x = adeleMap σ x := rfl

@[simp]
theorem adeleRingAut_symm_apply (σ : L ≃+* L) (x : AdeleRing (𝓞 L) L) :
    (adeleRingAut σ).symm x = adeleMap σ.symm x := rfl

/-- The action of the automorphism group of a number field `L` on its adele ring. -/
def adeleAut : RingAut L →* RingAut (AdeleRing (𝓞 L) L) where
  toFun := adeleRingAut
  map_one' := RingEquiv.ext fun x ↦ DFunLike.congr_fun adeleMap_refl x
  map_mul' σ τ := RingEquiv.ext fun x ↦ (DFunLike.congr_fun (adeleMap_trans τ σ) x).symm

@[simp]
theorem adeleAut_apply (σ : RingAut L) (x : AdeleRing (𝓞 L) L) :
    adeleAut σ x = adeleMap σ x := rfl

theorem adeleAut_injective : Function.Injective (adeleAut (L := L)) := by
  intro σ τ h
  refine RingEquiv.ext fun k ↦ ?_
  have := congrArg (fun F ↦ F (algebraMap L (AdeleRing (𝓞 L) L) k)) h
  simp only [adeleAut_apply, adeleMap_algebraMap] at this
  exact AdeleRing.algebraMap_injective (𝓞 L) L this

/-- The automorphism group of `L` acts on `𝔸_L` by ring automorphisms. -/
instance : MulSemiringAction (RingAut L) (AdeleRing (𝓞 L) L) :=
  MulSemiringAction.compHom _ adeleAut

@[simp]
theorem smul_adele_def (σ : RingAut L) (x : AdeleRing (𝓞 L) L) : σ • x = adeleMap σ x := rfl

end NumberField

/-! ## The action on the idele group -/

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- The action of the automorphism group of `L` on the idele group `𝕀_L = 𝔸_Lˣ`. -/
def ideleAut : RingAut L →* MulAut (IdeleGroup (𝓞 L) L) where
  toFun σ := Units.mapEquiv (adeleAut σ).toMulEquiv
  map_one' := by
    refine MulEquiv.ext fun u ↦ Units.ext ?_
    simp
  map_mul' σ τ := by
    refine MulEquiv.ext fun u ↦ Units.ext ?_
    simp

@[simp]
theorem coe_ideleAut (σ : RingAut L) (u : IdeleGroup (𝓞 L) L) :
    ((ideleAut σ u : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L) =
      adeleMap σ (u : AdeleRing (𝓞 L) L) := rfl

theorem ideleAut_principalEmbedding (σ : RingAut L) (x : Lˣ) :
    ideleAut σ (IdeleGroup.principalEmbedding (𝓞 L) L x) =
      IdeleGroup.principalEmbedding (𝓞 L) L (Units.mapEquiv σ.toMulEquiv x) := by
  refine Units.ext ?_
  simp

theorem ideleAut_map_principalSubgroup (σ : RingAut L) :
    (IdeleGroup.principalSubgroup (𝓞 L) L).map (ideleAut σ : IdeleGroup (𝓞 L) L →* _) =
      IdeleGroup.principalSubgroup (𝓞 L) L := by
  ext u
  simp only [Subgroup.mem_map, IdeleGroup.principalSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨Units.mapEquiv σ.toMulEquiv x, (ideleAut_principalEmbedding σ x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨IdeleGroup.principalEmbedding (𝓞 L) L (Units.mapEquiv σ.symm.toMulEquiv x),
      ⟨_, rfl⟩, Units.ext ?_⟩
    simp

/-- The automorphism group of `L` acts on `𝕀_L` by group automorphisms. -/
instance : MulDistribMulAction (RingAut L) (IdeleGroup (𝓞 L) L) :=
  MulDistribMulAction.compHom _ ideleAut

@[simp]
theorem smul_idele_def (σ : RingAut L) (u : IdeleGroup (𝓞 L) L) : σ • u = ideleAut σ u := rfl

/-! ## The action on the idele class group -/

/-- The action of the automorphism group of `L` on the idele class group `C_L = 𝕀_L / Lˣ`. -/
def ideleClassAut : RingAut L →* MulAut (IdeleClassGroup (𝓞 L) L) where
  toFun σ := QuotientGroup.congr _ _ (ideleAut σ) (ideleAut_map_principalSubgroup σ)
  map_one' := by
    refine MulEquiv.ext fun q ↦ QuotientGroup.induction_on q fun u ↦ ?_
    rw [QuotientGroup.congr_mk]
    simp
  map_mul' σ τ := by
    refine MulEquiv.ext fun q ↦ QuotientGroup.induction_on q fun u ↦ ?_
    rw [QuotientGroup.congr_mk]
    simp only [MulAut.mul_apply, map_mul]
    rw [QuotientGroup.congr_mk, QuotientGroup.congr_mk]

@[simp]
theorem ideleClassAut_mk (σ : RingAut L) (u : IdeleGroup (𝓞 L) L) :
    ideleClassAut σ (IdeleClassGroup.mk (𝓞 L) L u) =
      IdeleClassGroup.mk (𝓞 L) L (ideleAut σ u) :=
  QuotientGroup.congr_mk _ _ (ideleAut σ) (ideleAut_map_principalSubgroup σ) u

/-- The automorphism group of `L` acts on the idele class group `C_L`. -/
instance : MulDistribMulAction (RingAut L) (IdeleClassGroup (𝓞 L) L) :=
  MulDistribMulAction.compHom _ ideleClassAut

@[simp]
theorem smul_ideleClass_def (σ : RingAut L) (c : IdeleClassGroup (𝓞 L) L) :
    σ • c = ideleClassAut σ c := rfl

end NumberField

/-! ## The `Gal(L/K)`-action -/

namespace NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- `AlgEquiv.toRingEquiv` as a monoid homomorphism `Gal(L/K) →* RingAut L`. -/
def galToRingAut : (L ≃ₐ[K] L) →* RingAut L where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField L] in
@[simp]
theorem galToRingAut_apply (σ : L ≃ₐ[K] L) (x : L) : galToRingAut K L σ x = σ x := rfl

/-- The adele ring `𝔸_L` as a `Gal(L/K)`-object. -/
def galAdeleAut : (L ≃ₐ[K] L) →* RingAut (AdeleRing (𝓞 L) L) :=
  adeleAut.comp (galToRingAut K L)

/-- The idele group `𝕀_L` as a `Gal(L/K)`-object. -/
def galIdeleAut : (L ≃ₐ[K] L) →* MulAut (IdeleGroup (𝓞 L) L) :=
  ideleAut.comp (galToRingAut K L)

/-- The idele class group `C_L` as a `Gal(L/K)`-object. -/
def galIdeleClassAut : (L ≃ₐ[K] L) →* MulAut (IdeleClassGroup (𝓞 L) L) :=
  ideleClassAut.comp (galToRingAut K L)

variable {K L}

@[simp]
theorem galAdeleAut_apply (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    galAdeleAut K L σ x = adeleMap σ.toRingEquiv x := rfl

@[simp]
theorem galIdeleAut_apply (σ : L ≃ₐ[K] L) (u : IdeleGroup (𝓞 L) L) :
    galIdeleAut K L σ u = ideleAut (galToRingAut K L σ) u := rfl

@[simp]
theorem galIdeleClassAut_mk (σ : L ≃ₐ[K] L) (u : IdeleGroup (𝓞 L) L) :
    galIdeleClassAut K L σ (IdeleClassGroup.mk (𝓞 L) L u) =
      IdeleClassGroup.mk (𝓞 L) L (galIdeleAut K L σ u) :=
  ideleClassAut_mk _ u

/-- The image of the base field `K` inside `𝔸_L` is fixed by `Gal(L/K)`. -/
@[simp]
theorem galAdeleAut_algebraMap (σ : L ≃ₐ[K] L) (k : K) :
    galAdeleAut K L σ (algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L k)) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L k) := by
  rw [galAdeleAut_apply, adeleMap_algebraMap]
  simp

/-- The image of `Kˣ` inside `𝕀_L` is fixed by `Gal(L/K)`. -/
theorem galIdeleAut_principalEmbedding_algebraMap (σ : L ≃ₐ[K] L) (x : Kˣ) :
    galIdeleAut K L σ (IdeleGroup.principalEmbedding (𝓞 L) L (Units.map (algebraMap K L) x)) =
      IdeleGroup.principalEmbedding (𝓞 L) L (Units.map (algebraMap K L) x) := by
  refine Units.ext ?_
  simp

/-- The image of `Kˣ` inside `C_L` is fixed by `Gal(L/K)`. -/
theorem galIdeleClassAut_mk_principalEmbedding_algebraMap (σ : L ≃ₐ[K] L) (x : Kˣ) :
    galIdeleClassAut K L σ (IdeleClassGroup.mk (𝓞 L) L
        (IdeleGroup.principalEmbedding (𝓞 L) L (Units.map (algebraMap K L) x))) =
      IdeleClassGroup.mk (𝓞 L) L
        (IdeleGroup.principalEmbedding (𝓞 L) L (Units.map (algebraMap K L) x)) := by
  rw [galIdeleClassAut_mk, galIdeleAut_principalEmbedding_algebraMap]

end NumberField

/-! ## Continuity -/

namespace IsDedekindDomain.FiniteAdeleRing

variable {A B K L : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
  (e : A ≃+* B) (f : K ≃+* L) (hef : ∀ a : A, f (algebraMap A K a) = algebraMap B L (e a))

theorem continuous_congrRingHom : Continuous (congrRingHom e f hef) :=
  RestrictedProduct.mapAlong_continuous _ _ _
    ((equivOfRingEquiv e).symm.injective.tendsto_cofinite) _
    (Filter.Eventually.of_forall fun w ↦
      adicCompletionCongr_mapsTo_integers f _ w (valuation_symm_equivOfRingEquiv e f hef w))
    fun w ↦ continuous_adicCompletionCongr f _ w (valuation_symm_equivOfRingEquiv e f hef w)

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

theorem continuous_finiteAdeleMap (σ : L ≃+* L) : Continuous (finiteAdeleMap σ) :=
  FiniteAdeleRing.continuous_congrRingHom _ _ _

theorem continuous_adeleMap (σ : L ≃+* L) : Continuous (adeleMap σ) :=
  ((continuous_infiniteAdeleMap σ).prodMap (continuous_finiteAdeleMap σ)).comp continuous_id

/-- A field automorphism of `L` acts on `𝔸_L` by homeomorphisms. -/
def adeleHomeomorph (σ : L ≃+* L) : AdeleRing (𝓞 L) L ≃ₜ AdeleRing (𝓞 L) L where
  toEquiv := (adeleRingAut σ).toEquiv
  continuous_toFun := continuous_adeleMap σ
  continuous_invFun := continuous_adeleMap σ.symm

@[simp]
theorem adeleHomeomorph_apply (σ : L ≃+* L) (x : AdeleRing (𝓞 L) L) :
    adeleHomeomorph σ x = adeleMap σ x := rfl

theorem isOpenMap_adeleMap (σ : L ≃+* L) : IsOpenMap (adeleMap σ) :=
  (adeleHomeomorph σ).isOpenMap

end NumberField

/-! ## Stability of the principal subgroups, and the `Gal(L/K)`-actions as typeclasses -/

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

theorem adeleMap_map_principalSubgroup (σ : L ≃+* L) :
    (AdeleRing.principalSubgroup (𝓞 L) L).map (adeleMap σ : AdeleRing (𝓞 L) L →+ _) =
      AdeleRing.principalSubgroup (𝓞 L) L := by
  ext x
  simp only [AddSubgroup.mem_map, AdeleRing.principalSubgroup,
    Subring.mem_toAddSubgroup, RingHom.mem_range]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨σ k, (adeleMap_algebraMap σ k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨algebraMap L (AdeleRing (𝓞 L) L) (σ.symm k), ⟨σ.symm k, rfl⟩,
      (adeleMap_algebraMap σ (σ.symm k)).trans
        (congrArg (algebraMap L (AdeleRing (𝓞 L) L)) (σ.apply_symm_apply k))⟩

variable (K L)
variable [Field K] [Algebra K L]

/-- `𝔸_L` as a `Gal(L/K)`-ring. -/
@[instance_reducible] def galAdeleMulSemiringAction : MulSemiringAction (L ≃ₐ[K] L) (AdeleRing (𝓞 L) L) :=
  MulSemiringAction.compHom _ (galAdeleAut K L)

/-- `𝕀_L` as a `Gal(L/K)`-group. -/
@[instance_reducible] def galIdeleMulDistribMulAction : MulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup (𝓞 L) L) :=
  MulDistribMulAction.compHom _ (galIdeleAut K L)

/-- `C_L` as a `Gal(L/K)`-group. -/
@[instance_reducible] def galIdeleClassMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup (𝓞 L) L) :=
  MulDistribMulAction.compHom _ (galIdeleClassAut K L)

end NumberField
