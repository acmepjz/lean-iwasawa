/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing

@[expose] public section

/-!
# Functoriality of the infinite adele ring under isomorphisms

Mathlib has no functoriality for `AbsoluteValue.Completion` or for
`NumberField.InfinitePlace.Completion`.  This file supplies it: an isomorphism `f : K ≃+* L`
of fields carrying an infinite place `v` of `K` to an infinite place `w` of `L` (in the sense
that `w ∘ f = v`) induces an isomorphism of completions `v.Completion ≃+* w.Completion`, and
this construction is functorial.

This is the archimedean analogue of
`IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr`, and it is what is needed to define
the Galois action on the infinite adele ring of a number field, and hence (together with
`Iwasawalib.NumberTheory.CFT.FiniteAdeleCongr`) on the full adele ring.

## Main definitions

* `NumberField.InfinitePlace.Completion.withAbsCongr` : `f` as an isomorphism of the normed
  field synonyms `WithAbs v.1 ≃+* WithAbs w.1`.  It is an isometry.
* `NumberField.InfinitePlace.Completion.congr` : the induced isomorphism of completions.
* `NumberField.InfinitePlace.Completion.congrComap` : the special case
  `(v.comap σ).Completion ≃+* v.Completion` for `σ : L ≃+* L`.
* `NumberField.infiniteAdeleMap` : the ring homomorphism of `InfiniteAdeleRing L` induced by a
  field automorphism `σ : L ≃+* L`.
* `NumberField.infiniteAdeleRingAut`, `NumberField.infiniteAdeleAut` : the same packaged as a
  ring automorphism, and as a monoid homomorphism `RingAut L →* RingAut (InfiniteAdeleRing L)`.

## Main results

* `NumberField.InfinitePlace.Completion.isometry_congr` : the induced map is an isometry.
* `NumberField.InfinitePlace.Completion.congr_trans`, `congr_refl` : functoriality.
* `NumberField.infiniteAdeleMap_trans`, `infiniteAdeleMap_refl`.
-/

noncomputable section

open NumberField

namespace NumberField.InfinitePlace.Completion

section Congr

variable {K L M : Type*} [Field K] [Field L] [Field M] (f : K ≃+* L)
  (v : InfinitePlace K) (w : InfinitePlace L)

/-- A field isomorphism `f : K ≃+* L`, viewed as a map from `K` with the absolute value of the
infinite place `v` to `L` with the absolute value of the infinite place `w`. -/
def withAbsCongr : WithAbs v.1 ≃+* WithAbs w.1 := WithAbs.congr v.1 w.1 f

@[simp]
theorem withAbsCongr_apply (x : WithAbs v.1) :
    withAbsCongr f v w x = WithAbs.toAbs w.1 (f x.ofAbs) := rfl

variable (hf : ∀ x : K, w (f x) = v x)

include hf

theorem norm_withAbsCongr (x : WithAbs v.1) : ‖withAbsCongr f v w x‖ = ‖x‖ := hf x.ofAbs

/-- A field isomorphism carrying the absolute value of `v` to the absolute value of `w` is an
isometry `WithAbs v.1 → WithAbs w.1`. -/
theorem isometry_withAbsCongr : Isometry (withAbsCongr f v w) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_withAbsCongr f v w hf)

theorem norm_withAbsCongr_symm (y : WithAbs w.1) : ‖(withAbsCongr f v w).symm y‖ = ‖y‖ := by
  obtain ⟨x, rfl⟩ := (withAbsCongr f v w).surjective y
  rw [RingEquiv.symm_apply_apply, norm_withAbsCongr f v w hf]

theorem isometry_withAbsCongr_symm : Isometry (withAbsCongr f v w).symm :=
  AddMonoidHomClass.isometry_of_norm _ (norm_withAbsCongr_symm f v w hf)

/-- The isomorphism of completions `v.Completion ≃+* w.Completion` induced by a field
isomorphism `f : K ≃+* L` carrying the absolute value of `v` to the absolute value of `w`.

This is the archimedean analogue of
`IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr`. -/
def congr : v.Completion ≃+* w.Completion :=
  ((Completion.equiv v).trans
    (UniformSpace.Completion.mapRingEquiv (withAbsCongr f v w)
      (isometry_withAbsCongr f v w hf).continuous
      (isometry_withAbsCongr_symm f v w hf).continuous)).trans (Completion.equiv w).symm

theorem congr_apply (x : v.Completion) :
    congr f v w hf x =
      ofCompletion (UniformSpace.Completion.map (withAbsCongr f v w) x.toCompletion) := rfl

theorem continuous_congr : Continuous (congr f v w hf) :=
  (continuous_ofCompletion w).comp
    (UniformSpace.Completion.continuous_map.comp (continuous_toCompletion v))

@[simp]
theorem congr_coe (x : WithAbs v.1) :
    congr f v w hf (x : v.Completion) =
      ((WithAbs.toAbs w.1 (f x.ofAbs) : WithAbs w.1) : w.Completion) := by
  rw [congr_apply]
  congr 1
  exact UniformSpace.Completion.map_coe (isometry_withAbsCongr f v w hf).uniformContinuous _

@[simp]
theorem congr_algebraMap (k : K) :
    congr f v w hf (algebraMap K v.Completion k) = algebraMap L w.Completion (f k) :=
  congr_coe f v w hf (WithAbs.toAbs v.1 k)

/-- The induced map on completions is an isometry. -/
theorem isometry_congr : Isometry (congr f v w hf) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  induction x using induction_on with
  | hp =>
    refine isClosed_eq ?_ continuous_norm
    exact continuous_norm.comp (continuous_congr f v w hf)
  | ih a => rw [congr_coe, norm_coe, norm_coe]; exact hf _

end Congr

section Functorial

variable {K L M : Type*} [Field K] [Field L] [Field M]

theorem congr_trans (f : K ≃+* L) (g : L ≃+* M) (v : InfinitePlace K) (w : InfinitePlace L)
    (u : InfinitePlace M) (hf : ∀ x : K, w (f x) = v x) (hg : ∀ x : L, u (g x) = w x)
    (hfg : ∀ x : K, u (f.trans g x) = v x) (x : v.Completion) :
    congr g w u hg (congr f v w hf x) = congr (f.trans g) v u hfg x := by
  induction x using induction_on with
  | hp =>
    refine isClosed_eq ?_ (continuous_congr (f.trans g) v u hfg)
    exact (continuous_congr g w u hg).comp (continuous_congr f v w hf)
  | ih a => simp [congr_coe]

theorem congr_refl (v : InfinitePlace K) (hf : ∀ x : K, v (RingEquiv.refl K x) = v x)
    (x : v.Completion) : congr (RingEquiv.refl K) v v hf x = x := by
  induction x using induction_on with
  | hp => exact isClosed_eq (continuous_congr _ _ _ hf) continuous_id
  | ih a => simp [congr_coe]

end Functorial

end NumberField.InfinitePlace.Completion

/-! ## The action of a field automorphism on the infinite adele ring -/

namespace NumberField

open InfinitePlace

variable {L : Type*} [Field L]

/-- The isomorphism `(v.comap σ).Completion ≃+* v.Completion` induced by an automorphism
`σ : L ≃+* L`. -/
def InfinitePlace.Completion.congrComap (σ : L ≃+* L) (v : InfinitePlace L) :
    (v.comap (σ : L →+* L)).Completion ≃+* v.Completion :=
  Completion.congr σ (v.comap (σ : L →+* L)) v (fun _ ↦ rfl)

/-- The map induced on the infinite adele ring of `L` by a field automorphism `σ : L ≃+* L`:
the `v`-component of `σ • x` is `σ` applied to the `(v ∘ σ)`-component of `x`. -/
def infiniteAdeleMap (σ : L ≃+* L) : InfiniteAdeleRing L →+* InfiniteAdeleRing L where
  toFun x v := Completion.congrComap σ v (x (v.comap (σ : L →+* L)))
  map_one' := by funext v; exact map_one (Completion.congrComap σ v)
  map_mul' x y := by funext v; exact map_mul (Completion.congrComap σ v) _ _
  map_zero' := by funext v; exact map_zero (Completion.congrComap σ v)
  map_add' x y := by funext v; exact map_add (Completion.congrComap σ v) _ _

theorem infiniteAdeleMap_apply (σ : L ≃+* L) (x : InfiniteAdeleRing L) (v : InfinitePlace L) :
    infiniteAdeleMap σ x v = Completion.congrComap σ v (x (v.comap (σ : L →+* L))) := rfl

theorem continuous_infiniteAdeleMap (σ : L ≃+* L) : Continuous (infiniteAdeleMap σ) :=
  continuous_pi fun v ↦
    (Completion.continuous_congr σ _ v (fun _ ↦ rfl)).comp (continuous_apply _)

@[simp]
theorem infiniteAdeleMap_algebraMap (σ : L ≃+* L) (k : L) :
    infiniteAdeleMap σ (algebraMap L (InfiniteAdeleRing L) k) =
      algebraMap L (InfiniteAdeleRing L) (σ k) := by
  funext v
  exact Completion.congr_algebraMap σ _ v (fun _ ↦ rfl) k

theorem infiniteAdeleMap_trans (σ τ : L ≃+* L) :
    (infiniteAdeleMap τ).comp (infiniteAdeleMap σ) = infiniteAdeleMap (σ.trans τ) := by
  refine RingHom.ext fun x ↦ funext fun v ↦ ?_
  exact Completion.congr_trans σ τ _ _ v (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) _

theorem infiniteAdeleMap_refl :
    infiniteAdeleMap (RingEquiv.refl L) = RingHom.id (InfiniteAdeleRing L) := by
  refine RingHom.ext fun x ↦ funext fun v ↦ ?_
  exact Completion.congr_refl v (fun _ ↦ rfl) _

/-- The ring automorphism of the infinite adele ring of `L` induced by `σ : L ≃+* L`. -/
def infiniteAdeleRingAut (σ : L ≃+* L) : RingAut (InfiniteAdeleRing L) :=
  RingEquiv.ofRingHom (infiniteAdeleMap σ) (infiniteAdeleMap σ.symm)
    (by rw [infiniteAdeleMap_trans, RingEquiv.symm_trans_self, infiniteAdeleMap_refl])
    (by rw [infiniteAdeleMap_trans, RingEquiv.self_trans_symm, infiniteAdeleMap_refl])

@[simp]
theorem infiniteAdeleRingAut_apply (σ : L ≃+* L) (x : InfiniteAdeleRing L) :
    infiniteAdeleRingAut σ x = infiniteAdeleMap σ x := rfl

@[simp]
theorem infiniteAdeleRingAut_symm_apply (σ : L ≃+* L) (x : InfiniteAdeleRing L) :
    (infiniteAdeleRingAut σ).symm x = infiniteAdeleMap σ.symm x := rfl

/-- The action of the automorphism group of `L` on the infinite adele ring of `L`. -/
def infiniteAdeleAut : RingAut L →* RingAut (InfiniteAdeleRing L) where
  toFun := infiniteAdeleRingAut
  map_one' := RingEquiv.ext fun x ↦ DFunLike.congr_fun infiniteAdeleMap_refl x
  map_mul' σ τ := RingEquiv.ext fun x ↦
    (DFunLike.congr_fun (infiniteAdeleMap_trans τ σ) x).symm

@[simp]
theorem infiniteAdeleAut_apply (σ : RingAut L) (x : InfiniteAdeleRing L) :
    infiniteAdeleAut σ x = infiniteAdeleMap σ x := rfl

end NumberField

/-! ## The permutation of infinite places, and the adelic norm -/

namespace NumberField.InfinitePlace

variable {L : Type*} [Field L]

/-- Precomposition with a ring automorphism permutes the infinite places. -/
def comapEquiv (σ : L ≃+* L) : InfinitePlace L ≃ InfinitePlace L where
  toFun v := v.comap (σ : L →+* L)
  invFun v := v.comap (σ.symm : L →+* L)
  left_inv v := by
    show (v.comap (σ : L →+* L)).comap (σ.symm : L →+* L) = v
    rw [← comap_comp]
    convert comap_id v using 2
    exact RingHom.ext fun x ↦ σ.apply_symm_apply x
  right_inv v := by
    show (v.comap (σ.symm : L →+* L)).comap (σ : L →+* L) = v
    rw [← comap_comp]
    convert comap_id v using 2
    exact RingHom.ext fun x ↦ σ.symm_apply_apply x

@[simp] theorem comapEquiv_apply (σ : L ≃+* L) (v : InfinitePlace L) :
    comapEquiv σ v = v.comap (σ : L →+* L) := rfl

theorem mult_comap (σ : L ≃+* L) (v : InfinitePlace L) :
    (v.comap (σ : L →+* L)).mult = v.mult := by
  simp only [mult]
  rw [propext (isReal_comap_iff (f := σ))]

end NumberField.InfinitePlace

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- The action of a field automorphism on the infinite adele ring preserves the adelic norm. -/
theorem norm_infiniteAdeleMap (σ : L ≃+* L) (x : InfiniteAdeleRing L) :
    ‖infiniteAdeleMap σ x‖ = ‖x‖ := by
  rw [InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_def,
    ← Equiv.prod_comp (InfinitePlace.comapEquiv σ) (fun v ↦ ‖x v‖ ^ v.mult)]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [InfinitePlace.comapEquiv_apply, InfinitePlace.mult_comap, infiniteAdeleMap_apply]
  congr 1
  exact (InfinitePlace.Completion.isometry_congr σ _ v (fun _ ↦ rfl)).norm_map_of_map_zero
    (map_zero _) _

end NumberField
