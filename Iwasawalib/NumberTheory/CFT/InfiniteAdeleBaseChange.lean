/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.DecompositionSubgroup
public import Iwasawalib.NumberTheory.CFT.InfiniteAdeleCongr

@[expose] public section

/-!
# Base change and the semilocal decomposition of the infinite adele ring

For an extension of fields `K ⊆ L` and an infinite place `w` of `L` lying over the infinite
place `v = w.comap (algebraMap K L)` of `K`, the inclusion `K → L` is an isometry from `K`
with the absolute value of `v` to `L` with the absolute value of `w`, so it extends to a ring
homomorphism `v.Completion →+* w.Completion`.  Assembling these over all `w` gives the base
change map `𝔸_K^∞ →+* 𝔸_L^∞`, and its image consists of `Gal(L/K)`-invariant elements.

Grouping the infinite places of `L` by the place of `K` they lie over decomposes `𝔸_L^∞` as a
product of the *semilocal* factors `∏_{w ∣ v} L_w`, each of which is `Gal(L/K)`-stable; when
`L / K` is Galois the Galois group acts transitively on each fibre `{w ∣ v}` with stabiliser
the decomposition group of `w`.  This is the shape needed for Shapiro's lemma.

## Main definitions

* `NumberField.InfinitePlace.Completion.map` : the ring homomorphism of completions induced by
  a ring homomorphism of the base fields (the non-invertible version of
  `NumberField.InfinitePlace.Completion.congr`).
* `NumberField.InfiniteAdeleRing.baseChange : InfiniteAdeleRing K →+* InfiniteAdeleRing L`.
* `NumberField.InfiniteAdeleRing.Fibre v` : the infinite places of `L` above `v`.
* `NumberField.InfiniteAdeleRing.semilocalEquiv` : the ring isomorphism
  `𝔸_L^∞ ≃+* ∀ v, ∏_{w ∣ v} L_w`.

## Main results

* `NumberField.InfinitePlace.Completion.map_trans`, `map_id`, `isometry_map`.
* `NumberField.InfiniteAdeleRing.infiniteAdeleMap_baseChange` : the base change of `𝔸_K^∞` is
  pointwise fixed by `Gal(L/K)`.
* `NumberField.InfiniteAdeleRing.baseChange_injective`.
* `NumberField.InfiniteAdeleRing.semilocalEquiv_infiniteAdeleMap` : the decomposition is
  `Gal(L/K)`-equivariant, each semilocal factor being preserved.
* `NumberField.InfiniteAdeleRing.Fibre.exists_smul_eq` : transitivity on fibres.
* `NumberField.InfiniteAdeleRing.stabilizer_eq_decompositionSubgroup`.
-/

noncomputable section

open NumberField

namespace NumberField.InfinitePlace.Completion

variable {K L M : Type*} [Field K] [Field L] [Field M] (f : K →+* L)
  (v : InfinitePlace K) (w : InfinitePlace L)

/-- A ring hom `f : K →+* L`, viewed as a map `WithAbs v.1 →+* WithAbs w.1`. -/
def withAbsMap : WithAbs v.1 →+* WithAbs w.1 := WithAbs.map v.1 w.1 f

@[simp] theorem withAbsMap_apply (x : WithAbs v.1) :
    withAbsMap f v w x = WithAbs.toAbs w.1 (f x.ofAbs) := rfl

variable (hf : ∀ x : K, w (f x) = v x)
include hf

theorem norm_withAbsMap (x : WithAbs v.1) : ‖withAbsMap f v w x‖ = ‖x‖ := hf x.ofAbs

theorem isometry_withAbsMap : Isometry (withAbsMap f v w) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_withAbsMap f v w hf)

/-- The ring homomorphism of completions `v.Completion →+* w.Completion` induced by a ring
homomorphism `f : K →+* L` carrying the absolute value of `v` to that of `w`. -/
def map : v.Completion →+* w.Completion :=
  (Completion.equiv w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (withAbsMap f v w)
      (isometry_withAbsMap f v w hf).continuous).comp (Completion.equiv v).toRingHom)

theorem map_apply (x : v.Completion) :
    map f v w hf x =
      ofCompletion (UniformSpace.Completion.map (withAbsMap f v w) x.toCompletion) := rfl

theorem continuous_map : Continuous (map f v w hf) :=
  (continuous_ofCompletion w).comp
    (UniformSpace.Completion.continuous_map.comp (continuous_toCompletion v))

@[simp]
theorem map_coe (x : WithAbs v.1) :
    map f v w hf (x : v.Completion) =
      ((WithAbs.toAbs w.1 (f x.ofAbs) : WithAbs w.1) : w.Completion) := by
  rw [map_apply]
  congr 1
  exact UniformSpace.Completion.map_coe (isometry_withAbsMap f v w hf).uniformContinuous _

@[simp]
theorem map_algebraMap (k : K) :
    map f v w hf (algebraMap K v.Completion k) = algebraMap L w.Completion (f k) :=
  map_coe f v w hf (WithAbs.toAbs v.1 k)

theorem isometry_map : Isometry (map f v w hf) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  induction x using induction_on with
  | hp =>
    refine isClosed_eq ?_ continuous_norm
    exact continuous_norm.comp (continuous_map f v w hf)
  | ih a => rw [map_coe, norm_coe, norm_coe]; exact hf _

omit hf in
theorem congr_eq_map (g : K ≃+* L) (hg : ∀ x : K, w (g x) = v x) (x : v.Completion) :
    congr g v w hg x = map (g : K →+* L) v w hg x := rfl

end NumberField.InfinitePlace.Completion

namespace NumberField.InfinitePlace.Completion
variable {K L M : Type*} [Field K] [Field L] [Field M]

theorem map_trans (f : K →+* L) (g : L →+* M) (v : InfinitePlace K) (w : InfinitePlace L)
    (u : InfinitePlace M) (hf : ∀ x : K, w (f x) = v x) (hg : ∀ x : L, u (g x) = w x)
    (hgf : ∀ x : K, u (g.comp f x) = v x) (x : v.Completion) :
    map g w u hg (map f v w hf x) = map (g.comp f) v u hgf x := by
  induction x using induction_on with
  | hp =>
    refine isClosed_eq ?_ (continuous_map (g.comp f) v u hgf)
    exact (continuous_map g w u hg).comp (continuous_map f v w hf)
  | ih a => simp [map_coe]

theorem map_id (v : InfinitePlace K) (hf : ∀ x : K, v (RingHom.id K x) = v x)
    (x : v.Completion) : map (RingHom.id K) v v hf x = x := by
  induction x using induction_on with
  | hp => exact isClosed_eq (continuous_map _ _ _ hf) continuous_id
  | ih a => simp [map_coe]

/-- Transport of `map` along an equality of source places. -/
theorem map_index_congr {v₁ v₂ : InfinitePlace K} (h : v₁ = v₂) (f : K →+* L)
    (w : InfinitePlace L) (h₁ : ∀ x : K, w (f x) = v₁ x) (h₂ : ∀ x : K, w (f x) = v₂ x)
    (x : InfiniteAdeleRing K) : map f v₁ w h₁ (x v₁) = map f v₂ w h₂ (x v₂) := by
  subst h; rfl

end NumberField.InfinitePlace.Completion

namespace NumberField.InfinitePlace.Completion
variable {K L : Type*} [Field K] [Field L]

/-- Transport of `map` along an equality of the ring homomorphism. -/
theorem map_hom_congr {f g : K →+* L} (h : f = g) (v : InfinitePlace K) (w : InfinitePlace L)
    (hf : ∀ x : K, w (f x) = v x) (hg : ∀ x : K, w (g x) = v x) (x : v.Completion) :
    map f v w hf x = map g v w hg x := by subst h; rfl

end NumberField.InfinitePlace.Completion

/-! ## Base change of the infinite adele ring -/

namespace NumberField.InfiniteAdeleRing

open InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The base change map `𝔸_K^∞ →+* 𝔸_L^∞`: the `w`-component of `baseChange x` is the image
of the component of `x` at the place of `K` below `w`. -/
def baseChange : InfiniteAdeleRing K →+* InfiniteAdeleRing L where
  toFun x w := Completion.map (algebraMap K L) (w.comap (algebraMap K L)) w (fun _ ↦ rfl)
    (x (w.comap (algebraMap K L)))
  map_one' := by
    funext w
    exact map_one (Completion.map (algebraMap K L) (w.comap (algebraMap K L)) w (fun _ ↦ rfl))
  map_mul' x y := by
    funext w
    exact map_mul (Completion.map (algebraMap K L) (w.comap (algebraMap K L)) w (fun _ ↦ rfl)) _ _
  map_zero' := by
    funext w
    exact map_zero (Completion.map (algebraMap K L) (w.comap (algebraMap K L)) w (fun _ ↦ rfl))
  map_add' x y := by
    funext w
    exact map_add (Completion.map (algebraMap K L) (w.comap (algebraMap K L)) w (fun _ ↦ rfl)) _ _

theorem baseChange_apply (x : InfiniteAdeleRing K) (w : InfinitePlace L) :
    baseChange x w = Completion.map (algebraMap K L) (w.comap (algebraMap K L)) w (fun _ ↦ rfl)
      (x (w.comap (algebraMap K L))) := rfl

theorem continuous_baseChange : Continuous (baseChange (K := K) (L := L)) :=
  continuous_pi fun w ↦
    (Completion.continuous_map (algebraMap K L) _ w (fun _ ↦ rfl)).comp (continuous_apply _)

@[simp]
theorem baseChange_algebraMap (k : K) :
    baseChange (algebraMap K (InfiniteAdeleRing K) k) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L k) := by
  funext w
  exact Completion.map_algebraMap (algebraMap K L) _ w (fun _ ↦ rfl) k

theorem baseChange_injective [Algebra.IsAlgebraic K L] :
    Function.Injective (baseChange (K := K) (L := L)) := by
  intro x y hxy
  funext v
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  have h := congrFun hxy w
  rw [baseChange_apply, baseChange_apply] at h
  exact (Completion.isometry_map (algebraMap K L) _ w (fun _ ↦ rfl)).injective h

end NumberField.InfiniteAdeleRing

/-! ## The base change is `Gal(L/K)`-invariant -/

namespace NumberField.InfiniteAdeleRing

open InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem comap_algebraMap_comp (σ : L ≃ₐ[K] L) :
    ((σ : L ≃+* L) : L →+* L).comp (algebraMap K L) = algebraMap K L :=
  RingHom.ext fun k ↦ σ.commutes k

theorem comap_comap_algEquiv (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    (w.comap ((σ : L ≃+* L) : L →+* L)).comap (algebraMap K L) = w.comap (algebraMap K L) := by
  rw [← InfinitePlace.comap_comp, comap_algebraMap_comp]

/-- The infinite adeles coming from the base field are fixed by `Gal(L/K)`. -/
theorem infiniteAdeleMap_baseChange (σ : L ≃ₐ[K] L) (x : InfiniteAdeleRing K) :
    infiniteAdeleMap (σ : L ≃+* L) (baseChange x) = baseChange x := by
  funext w
  have hσ := comap_algebraMap_comp σ
  have h1 := comap_comap_algEquiv σ w
  have h2 : ∀ k : K, (w.comap ((σ : L ≃+* L) : L →+* L)) (algebraMap K L k) =
      (w.comap (algebraMap K L)) k := by
    intro k
    rw [← InfinitePlace.comap_apply, h1]
  have h3 : ∀ k : K, w (((σ : L ≃+* L) : L →+* L).comp (algebraMap K L) k) =
      (w.comap (algebraMap K L)) k := by
    intro k
    rw [hσ]
    rfl
  calc infiniteAdeleMap (σ : L ≃+* L) (baseChange x) w
      = Completion.map ((σ : L ≃+* L) : L →+* L) (w.comap ((σ : L ≃+* L) : L →+* L)) w
          (fun _ ↦ rfl)
          (Completion.map (algebraMap K L)
            ((w.comap ((σ : L ≃+* L) : L →+* L)).comap (algebraMap K L))
            (w.comap ((σ : L ≃+* L) : L →+* L)) (fun _ ↦ rfl)
            (x ((w.comap ((σ : L ≃+* L) : L →+* L)).comap (algebraMap K L)))) := rfl
    _ = Completion.map ((σ : L ≃+* L) : L →+* L) (w.comap ((σ : L ≃+* L) : L →+* L)) w
          (fun _ ↦ rfl)
          (Completion.map (algebraMap K L) (w.comap (algebraMap K L))
            (w.comap ((σ : L ≃+* L) : L →+* L)) h2 (x (w.comap (algebraMap K L)))) := by
        rw [Completion.map_index_congr h1 (algebraMap K L)
          (w.comap ((σ : L ≃+* L) : L →+* L)) (fun _ ↦ rfl) h2 x]
    _ = Completion.map (((σ : L ≃+* L) : L →+* L).comp (algebraMap K L))
          (w.comap (algebraMap K L)) w h3 (x (w.comap (algebraMap K L))) :=
        Completion.map_trans _ _ _ _ _ _ _ _ _
    _ = Completion.map (algebraMap K L) (w.comap (algebraMap K L)) w (fun _ ↦ rfl)
          (x (w.comap (algebraMap K L))) := Completion.map_hom_congr hσ _ _ _ _ _
    _ = baseChange x w := rfl

end NumberField.InfiniteAdeleRing

/-! ## The semilocal decomposition -/

namespace NumberField.InfiniteAdeleRing

open InfinitePlace

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

theorem algEquiv_comp_algebraMap (σ : L ≃ₐ[K] L) :
    ((σ : L →+* L)).comp (algebraMap K L) = algebraMap K L :=
  RingHom.ext fun k ↦ σ.commutes k

variable {L}

theorem comap_comap_algEquiv' (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    (w.comap (σ : L →+* L)).comap (algebraMap K L) = w.comap (algebraMap K L) := by
  rw [← InfinitePlace.comap_comp, algEquiv_comp_algebraMap]

variable (L)

/-- The infinite places of `L` lying above an infinite place `v` of `K`. -/
abbrev Fibre (v : InfinitePlace K) : Type _ :=
  {w : InfinitePlace L // w.comap (algebraMap K L) = v}

namespace Fibre

variable {L} {v : InfinitePlace K}

theorem comap_eq (w : Fibre L v) : (w : InfinitePlace L).comap (algebraMap K L) = v := w.2

instance : MulAction (L ≃ₐ[K] L) (Fibre L v) where
  smul σ w := ⟨σ • (w : InfinitePlace L), by
    rw [InfinitePlace.smul_eq_comap, comap_comap_algEquiv']
    exact w.2⟩
  one_smul w := Subtype.ext (one_smul _ _)
  mul_smul a b w := Subtype.ext (mul_smul _ _ _)

@[simp] theorem coe_smul (σ : L ≃ₐ[K] L) (w : Fibre L v) :
    ((σ • w : Fibre L v) : InfinitePlace L) = σ • (w : InfinitePlace L) := rfl

/-- `Gal(L/K)` acts transitively on the infinite places above a fixed place of `K`. -/
theorem exists_smul_eq [IsGalois K L] (w w' : Fibre L v) : ∃ σ : L ≃ₐ[K] L, σ • w = w' := by
  obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq
    (k := K) (w := (w : InfinitePlace L)) (w' := (w' : InfinitePlace L)) (w.2.trans w'.2.symm)
  exact ⟨σ, Subtype.ext hσ⟩

instance [IsGalois K L] : MulAction.IsPretransitive (L ≃ₐ[K] L) (Fibre L v) :=
  ⟨fun w w' ↦ exists_smul_eq w w'⟩

end Fibre

variable {L}

/-- The stabiliser of an infinite place of `L` in `Gal(L/K)` is its decomposition subgroup. -/
theorem stabilizer_eq_decompositionSubgroup (w : InfinitePlace L) :
    MulAction.stabilizer (L ≃ₐ[K] L) w = AbsoluteValue.decompositionSubgroup K w.1 := by
  ext σ
  rw [AbsoluteValue.decompositionSubgroup, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

variable (L)

/-- The infinite adele ring of `L` is the product over the infinite places `v` of `K` of the
semilocal factors `∏_{w ∣ v} L_w`. -/
def semilocalEquiv :
    InfiniteAdeleRing L ≃+*
      ∀ v : InfinitePlace K, ∀ w : Fibre L v, (w : InfinitePlace L).Completion where
  toFun x v w := x (w : InfinitePlace L)
  invFun y w := y (w.comap (algebraMap K L)) ⟨w, rfl⟩
  left_inv x := rfl
  right_inv y := by
    funext v w
    obtain ⟨w, rfl⟩ := w
    rfl
  map_mul' x y := rfl
  map_add' x y := rfl

variable {L}

@[simp]
theorem semilocalEquiv_apply (x : InfiniteAdeleRing L) (v : InfinitePlace K) (w : Fibre L v) :
    semilocalEquiv L x v w = x (w : InfinitePlace L) := rfl

@[simp]
theorem semilocalEquiv_symm_apply
    (y : ∀ v : InfinitePlace K, ∀ w : Fibre L v, (w : InfinitePlace L).Completion)
    (w : InfinitePlace L) :
    (semilocalEquiv L).symm y w = y (w.comap (algebraMap K L)) ⟨w, rfl⟩ := rfl

/-- The semilocal decomposition is `Gal(L/K)`-equivariant: each factor `∏_{w ∣ v} L_w` is
preserved, `σ` sending the `(w ∘ σ)`-component to the `w`-component. -/
theorem semilocalEquiv_infiniteAdeleMap (σ : L ≃ₐ[K] L) (x : InfiniteAdeleRing L)
    (v : InfinitePlace K) (w : Fibre L v) :
    semilocalEquiv L (infiniteAdeleMap (σ : L ≃+* L) x) v w =
      Completion.congrComap (σ : L ≃+* L) (w : InfinitePlace L)
        (semilocalEquiv L x v
          ⟨(w : InfinitePlace L).comap ((σ : L ≃+* L) : L →+* L),
            (comap_comap_algEquiv σ _).trans w.2⟩) := rfl

end NumberField.InfiniteAdeleRing

/-! ## Orbit-stabiliser for the fibre: the index set of the induced module -/

namespace NumberField.InfiniteAdeleRing.Fibre

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] {v : InfinitePlace K}

instance [Algebra.IsAlgebraic K L] : Nonempty (Fibre L v) :=
  let ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  ⟨⟨w, hw⟩⟩

theorem stabilizer_eq (w : Fibre L v) :
    MulAction.stabilizer (L ≃ₐ[K] L) w =
      MulAction.stabilizer (L ≃ₐ[K] L) (w : InfinitePlace L) := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, Subtype.ext_iff, coe_smul]

theorem stabilizer_eq_decompositionSubgroup (w : Fibre L v) :
    MulAction.stabilizer (L ≃ₐ[K] L) w =
      AbsoluteValue.decompositionSubgroup K (w : InfinitePlace L).1 :=
  (stabilizer_eq w).trans (InfiniteAdeleRing.stabilizer_eq_decompositionSubgroup _)

/-- Orbit-stabiliser for infinite places: as a `Gal(L/K)`-set the fibre above `v` is the coset
space `Gal(L/K) ⧸ D_w`.  This is the index set of the induced module `Ind_{D_w}^{G} L_w`. -/
def equivQuotientStabilizer [IsGalois K L] (w : Fibre L v) :
    Fibre L v ≃ (L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L) w :=
  ((Equiv.Set.univ (Fibre L v)).symm.trans
    (Equiv.setCongr (MulAction.orbit_eq_univ (L ≃ₐ[K] L) w).symm)).trans
      (MulAction.orbitEquivQuotientStabilizer (L ≃ₐ[K] L) w)

@[simp]
theorem equivQuotientStabilizer_symm_apply [IsGalois K L] (w : Fibre L v)
    (g : L ≃ₐ[K] L) :
    (equivQuotientStabilizer w).symm (QuotientGroup.mk g) = g • w :=
  MulAction.orbitEquivQuotientStabilizer_symm_apply (L ≃ₐ[K] L) w g

end NumberField.InfiniteAdeleRing.Fibre
