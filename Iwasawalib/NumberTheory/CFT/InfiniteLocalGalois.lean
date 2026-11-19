/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.InfiniteAdeleBaseChange
public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

/-!
# Galois theory of the archimedean completions

For `L / K` a finite Galois extension of number fields and `w` an infinite place of `L` lying
over the infinite place `v` of `K`, the completion `L_w` is a finite Galois extension of `K_v`
whose Galois group is the decomposition group of `w`.
-/

noncomputable section

open NumberField NumberField.InfinitePlace IntermediateField
open scoped NumberField.LiesOver IntermediateField

namespace NumberField.InfinitePlace

section Basic

variable {K : Type*} [Field K] [NumberField K] (v : InfinitePlace K)

instance charZero_completion : CharZero v.Completion :=
  (Completion.extensionEmbedding v).charZero

instance nontriviallyNormedField_completion : NontriviallyNormedField v.Completion :=
  { (inferInstance : NormedField v.Completion) with
    non_trivial := by
      refine ⟨(2 : v.Completion), ?_⟩
      have h := (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero _) (2 : v.Completion)
      rw [← h, map_ofNat]
      norm_num }

omit [NumberField K] in
theorem denseRange_algebraMap_completion : DenseRange (algebraMap K v.Completion) := by
  have h := Completion.denseRange_coe (v := v)
  have hr : Set.range (fun x : WithAbs v.1 ↦ (x : v.Completion))
      = Set.range (algebraMap K v.Completion) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨WithAbs.ofAbs x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨WithAbs.toAbs v.1 x, rfl⟩
  rw [DenseRange, ← hr]
  exact h

omit [NumberField K] in
theorem norm_algebraMap_completion (y : K) : ‖algebraMap K v.Completion y‖ = v y :=
  Completion.norm_coe v (WithAbs.toAbs v.1 y)

/-- The embedding of `K` with its `v`-metric into the completion `K_v`, as a ring hom. -/
def coeRingHom : WithAbs v.1 →+* v.Completion :=
  (algebraMap K v.Completion).comp (WithAbs.equiv v.1).toRingHom

omit [NumberField K] in
@[simp]
theorem coeRingHom_apply (x : WithAbs v.1) : coeRingHom v x = (x : v.Completion) := rfl

omit [NumberField K] in
theorem isometry_coeRingHom : Isometry (coeRingHom v) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ Completion.norm_coe v x

end Basic

section Finite

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

instance isScalarTower_completion : IsScalarTower K L w.Completion :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- **`L_w` is spanned over `K_v` by the image of `L`.** -/
theorem span_range_algebraMap_completion_eq_top :
    Submodule.span v.Completion (Set.range (algebraMap L w.Completion)) = ⊤ := by
  classical
  set b := Module.finBasis K L with hb
  set S : Submodule v.Completion w.Completion :=
    Submodule.span _ (Set.range fun i ↦ algebraMap L w.Completion (b i)) with hS
  have hfin : Module.Finite v.Completion S :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  have hsub : Set.range (algebraMap L w.Completion) ⊆ (S : Set w.Completion) := by
    rintro _ ⟨y, rfl⟩
    have hy := b.sum_repr y
    rw [← hy, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul]
    have hc : algebraMap L w.Completion (algebraMap K L (b.repr y i))
        = algebraMap v.Completion w.Completion (algebraMap K v.Completion (b.repr y i)) := by
      rw [← IsScalarTower.algebraMap_apply K L w.Completion,
        ← IsScalarTower.algebraMap_apply K v.Completion w.Completion]
    rw [hc, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hclosed : IsClosed (S : Set w.Completion) := S.closed_of_finiteDimensional
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact hclosed.closure_subset_iff.2 hsub (denseRange_algebraMap_completion w x)
  refine eq_top_iff.2 ?_
  rw [← htop]
  exact Submodule.span_mono (Set.range_subset_iff.2 fun i ↦ ⟨b i, rfl⟩)

/-- **`L_w / K_v` is a finite extension.** -/
instance module_finite_completion : Module.Finite v.Completion w.Completion := by
  classical
  set b := Module.finBasis K L with hb
  refine ⟨⟨Finset.image (fun i ↦ algebraMap L w.Completion (b i)) Finset.univ, ?_⟩⟩
  rw [eq_top_iff, ← span_range_algebraMap_completion_eq_top v w]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, rfl⟩
  have hy := b.sum_repr y
  rw [← hy, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul]
  have hc : algebraMap L w.Completion (algebraMap K L (b.repr y i))
      = algebraMap v.Completion w.Completion (algebraMap K v.Completion (b.repr y i)) := by
    rw [← IsScalarTower.algebraMap_apply K L w.Completion,
      ← IsScalarTower.algebraMap_apply K v.Completion w.Completion]
  rw [hc, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

end Finite

section Normal

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

/-- `L_w` is generated as a `K_v`-algebra by the image of `L`. -/
theorem adjoin_range_algebraMap_completion_eq_top :
    Algebra.adjoin v.Completion (Set.range (algebraMap L w.Completion)) = ⊤ := by
  have h : Submodule.span v.Completion (Set.range (algebraMap L w.Completion))
      ≤ Subalgebra.toSubmodule
        (Algebra.adjoin v.Completion (Set.range (algebraMap L w.Completion))) :=
    Submodule.span_le.2 Algebra.subset_adjoin
  refine eq_top_iff.2 fun x _ ↦ ?_
  exact h (by rw [span_range_algebraMap_completion_eq_top]; trivial)

/-- If `α` generates `L` over `K`, then its image generates `L_w` over `K_v`. -/
theorem adjoin_singleton_completion_eq_top {α : L} (hα : K⟮α⟯ = ⊤) :
    Algebra.adjoin v.Completion {algebraMap L w.Completion α} = ⊤ := by
  rw [eq_top_iff, ← adjoin_range_algebraMap_completion_eq_top v w, Algebra.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ Algebra.adjoin K ({α} : Set L) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite K α), IntermediateField.mem_toSubalgebra, hα]
    exact IntermediateField.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Algebra.subset_adjoin rfl
  | algebraMap c =>
      rw [← IsScalarTower.algebraMap_apply K L w.Completion,
        IsScalarTower.algebraMap_apply K v.Completion w.Completion]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

omit [NumberField K] [NumberField L] in
theorem aeval_algebraMap_minpoly_map_completion (α : L) :
    (Polynomial.aeval (algebraMap L w.Completion α))
      ((minpoly K α).map (algebraMap K v.Completion)) = 0 := by
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
    minpoly.aeval, map_zero]

variable [IsGalois K L]

theorem isSplittingField_completion {α : L} (hα : K⟮α⟯ = ⊤) :
    Polynomial.IsSplittingField v.Completion w.Completion
      ((minpoly K α).map (algebraMap K v.Completion)) where
  splits' := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq K L w.Completion, ← Polynomial.map_map]
    exact (IsGalois.to_normal.splits α).map _
  adjoin_rootSet' := by
    have hne : (minpoly K α) ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite K α)
    have hmapne : ((minpoly K α).map (algebraMap K v.Completion)).map
        (algebraMap v.Completion w.Completion) ≠ 0 := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      exact Polynomial.map_ne_zero hne
    have hroot : algebraMap L w.Completion α ∈
        ((minpoly K α).map (algebraMap K v.Completion)).rootSet w.Completion :=
      Polynomial.mem_rootSet'.2 ⟨hmapne, aeval_algebraMap_minpoly_map_completion v w α⟩
    refine eq_top_iff.2 ?_
    rw [← adjoin_singleton_completion_eq_top v w hα]
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 hroot)

/-- **`L_w / K_v` is normal.** -/
instance normal_completion : Normal v.Completion w.Completion := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  haveI := isSplittingField_completion v w hα
  exact Normal.of_isSplittingField ((minpoly K α).map (algebraMap K v.Completion))

/-- **`L_w / K_v` is a finite Galois extension.** -/
instance isGalois_completion : IsGalois v.Completion w.Completion where

end Normal

section LocalGal

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

/-- An automorphism of `L` preserving the place `w` induces a `K_v`-automorphism of `L_w`. -/
def localAut (σ : L ≃ₐ[K] L) (hσ : ∀ y : L, w ((σ : L ≃+* L) y) = w y) :
    w.Completion ≃ₐ[v.Completion] w.Completion :=
  { Completion.congr (σ : L ≃+* L) w w hσ with
    commutes' := by
      have hcont₁ : Continuous fun c : v.Completion ↦
          Completion.congr (σ : L ≃+* L) w w hσ (algebraMap v.Completion w.Completion c) :=
        (Completion.continuous_congr _ w w hσ).comp (NumberField.LiesOver.continuous_completionMap _ _)
      have hcont₂ : Continuous (algebraMap v.Completion w.Completion) :=
        (NumberField.LiesOver.continuous_completionMap _ _)
      have := Continuous.ext_on (denseRange_algebraMap_completion v) hcont₁ hcont₂ ?_
      · exact fun c ↦ congrFun this c
      · rintro _ ⟨k, rfl⟩
        show Completion.congr (σ : L ≃+* L) w w hσ
            (algebraMap v.Completion w.Completion (algebraMap K v.Completion k))
          = algebraMap v.Completion w.Completion (algebraMap K v.Completion k)
        rw [← IsScalarTower.algebraMap_apply K v.Completion w.Completion,
          IsScalarTower.algebraMap_apply K L w.Completion, Completion.congr_algebraMap]
        exact congrArg _ (σ.commutes k) }

omit [NumberField K] [NumberField L] in
@[simp]
theorem localAut_algebraMap (σ : L ≃ₐ[K] L) (hσ : ∀ y : L, w ((σ : L ≃+* L) y) = w y) (y : L) :
    localAut v w σ hσ (algebraMap L w.Completion y) = algebraMap L w.Completion (σ y) :=
  Completion.congr_algebraMap (σ : L ≃+* L) w w hσ y

variable [IsGalois K L]

omit [IsGalois K L] in
/-- Every `K_v`-automorphism of `L_w` is continuous: it is a `K_v`-linear map on a
finite-dimensional space. -/
theorem continuous_algEquiv (τ : w.Completion ≃ₐ[v.Completion] w.Completion) :
    Continuous τ :=
  τ.toLinearMap.continuous_of_finiteDimensional

/-- **The restriction of a `K_v`-automorphism of `L_w` to `L`.** -/
def restrictLocal (τ : w.Completion ≃ₐ[v.Completion] w.Completion) : L ≃ₐ[K] L :=
  AlgEquiv.restrictNormalHom L (τ.restrictScalars K)

omit [NumberField K] [NumberField L] in
theorem algebraMap_restrictLocal (τ : w.Completion ≃ₐ[v.Completion] w.Completion) (y : L) :
    algebraMap L w.Completion (restrictLocal v w τ y) = τ (algebraMap L w.Completion y) :=
  AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L y

/-- The restriction of a `K_v`-automorphism of `L_w` preserves the place `w`. -/
theorem restrictLocal_apply_eq (τ : w.Completion ≃ₐ[v.Completion] w.Completion) (y : L) :
    w (restrictLocal v w τ y) = w y := by
  have hcont : Continuous (WithAbs.congr w.1 w.1 (restrictLocal v w τ)) := by
    refine ((isometry_coeRingHom w).isEmbedding).continuous_iff.2 ?_
    have hcomm : (coeRingHom w) ∘ (WithAbs.congr w.1 w.1 (restrictLocal v w τ))
        = τ ∘ (coeRingHom w) := by
      funext x
      exact algebraMap_restrictLocal v w τ _
    rw [hcomm]
    exact (continuous_algEquiv v w τ).comp (isometry_coeRingHom w).continuous
  have hmem : restrictLocal v w τ ∈ (w.1).decompositionSubgroup K :=
    (AbsoluteValue.mem_decompositionSubgroup_iff_continuous (F := K) (K := L)
      w.1 (restrictLocal v w τ)).2 hcont
  exact (AbsoluteValue.mem_decompositionSubgroup_iff_forall_apply_eq
    w.1 (restrictLocal v w τ)).1 hmem y

omit [NumberField K] [NumberField L] [IsGalois K L] [w.LiesOver v] in
theorem mem_stabilizer_iff_apply_eq {σ : L ≃ₐ[K] L} :
    σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w ↔ ∀ y : L, w (σ y) = w y := by
  rw [InfiniteAdeleRing.stabilizer_eq_decompositionSubgroup w]
  exact AbsoluteValue.mem_decompositionSubgroup_iff_forall_apply_eq w.1 σ

/-- **The decomposition group of `w` maps to `Gal(L_w/K_v)`.** -/
def toLocalGal (d : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    w.Completion ≃ₐ[v.Completion] w.Completion :=
  localAut v w d (mem_stabilizer_iff_apply_eq w |>.1 d.2)

omit [NumberField K] [NumberField L] [IsGalois K L] in
@[simp]
theorem toLocalGal_algebraMap (d : MulAction.stabilizer (L ≃ₐ[K] L) w) (y : L) :
    toLocalGal v w d (algebraMap L w.Completion y)
      = algebraMap L w.Completion ((d : L ≃ₐ[K] L) y) :=
  localAut_algebraMap v w _ _ y

omit [NumberField K] [NumberField L] in
theorem restrictLocal_toLocalGal (d : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    restrictLocal v w (toLocalGal v w d) = (d : L ≃ₐ[K] L) :=
  AlgEquiv.ext fun y ↦ (algebraMap L w.Completion).injective
    ((algebraMap_restrictLocal v w _ y).trans (toLocalGal_algebraMap v w d y))

theorem toLocalGal_restrictLocal (τ : w.Completion ≃ₐ[v.Completion] w.Completion) :
    toLocalGal v w ⟨restrictLocal v w τ,
      (mem_stabilizer_iff_apply_eq w).2 (restrictLocal_apply_eq v w τ)⟩ = τ := by
  have h : (toLocalGal v w ⟨restrictLocal v w τ,
      (mem_stabilizer_iff_apply_eq w).2 (restrictLocal_apply_eq v w τ)⟩ :
        w.Completion ≃ₐ[v.Completion] w.Completion).toAlgHom = τ.toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (adjoin_range_algebraMap_completion_eq_top v w) ?_
    rintro _ ⟨y, rfl⟩
    show toLocalGal v w _ (algebraMap L w.Completion y) = τ (algebraMap L w.Completion y)
    rw [← algebraMap_restrictLocal v w τ y]
    exact toLocalGal_algebraMap v w _ y
  exact AlgEquiv.ext fun x ↦ AlgHom.congr_fun h x

/-- **`D_w ≃ Gal(L_w/K_v)`** at an infinite place. -/
def stabilizerEquivLocalGal :
    MulAction.stabilizer (L ≃ₐ[K] L) w ≃* (w.Completion ≃ₐ[v.Completion] w.Completion) where
  toFun := toLocalGal v w
  invFun τ := ⟨restrictLocal v w τ,
    (mem_stabilizer_iff_apply_eq w).2 (restrictLocal_apply_eq v w τ)⟩
  left_inv d := Subtype.ext (restrictLocal_toLocalGal v w d)
  right_inv τ := toLocalGal_restrictLocal v w τ
  map_mul' d d' := by
    refine AlgEquiv.ext fun x ↦ ?_
    exact (Completion.congr_trans ((d' : L ≃ₐ[K] L) : L ≃+* L) ((d : L ≃ₐ[K] L) : L ≃+* L)
      w w w ((mem_stabilizer_iff_apply_eq w).1 d'.2) ((mem_stabilizer_iff_apply_eq w).1 d.2)
      ((mem_stabilizer_iff_apply_eq w).1 (d * d').2) x).symm

theorem toLocalGal_surjective : Function.Surjective (toLocalGal v w) :=
  (stabilizerEquivLocalGal v w).surjective

/-- **`L_w^{D_w} = K_v`** at an infinite place: an element of `L_w` fixed by the decomposition
group of `w` lies in the image of `K_v`. -/
theorem mem_range_algebraMap_of_fixed {x : w.Completion}
    (hx : ∀ d : MulAction.stabilizer (L ≃ₐ[K] L) w, toLocalGal v w d x = x) :
    x ∈ Set.range (algebraMap v.Completion w.Completion) := by
  refine (IsGalois.mem_range_algebraMap_iff_fixed x).2 fun f ↦ ?_
  obtain ⟨d, rfl⟩ := toLocalGal_surjective v w f
  exact hx d

end LocalGal

section Transport

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- `Completion.map` along the structure map is the algebra map of completions. -/
theorem completionMap_eq_algebraMap (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (hf : ∀ x : K, w (algebraMap K L x) = v x) (c : v.Completion) :
    Completion.map (algebraMap K L) v w hf c = algebraMap v.Completion w.Completion c := by
  have hcont₁ : Continuous (Completion.map (algebraMap K L) v w hf) :=
    Completion.continuous_map _ v w hf
  have hcont₂ : Continuous (algebraMap v.Completion w.Completion) :=
    (NumberField.LiesOver.continuous_completionMap _ _)
  have := Continuous.ext_on (denseRange_algebraMap_completion v) hcont₁ hcont₂ ?_
  · exact congrFun this c
  · rintro _ ⟨k, rfl⟩
    rw [Completion.map_algebraMap, ← IsScalarTower.algebraMap_apply K v.Completion w.Completion,
      IsScalarTower.algebraMap_apply K L w.Completion]

omit [NumberField K] [NumberField L] in
/-- Transporting the algebra map of completions along an automorphism of `L`. -/
theorem congr_algebraMap_completion (v : InfinitePlace K) (w₀ w : InfinitePlace L)
    [w₀.LiesOver v] [w.LiesOver v] (σ : L ≃ₐ[K] L)
    (h : ∀ y : L, w ((σ : L ≃+* L) y) = w₀ y) (c : v.Completion) :
    Completion.congr (σ : L ≃+* L) w₀ w h (algebraMap v.Completion w₀.Completion c)
      = algebraMap v.Completion w.Completion c := by
  have hcont₁ : Continuous fun c : v.Completion ↦
      Completion.congr (σ : L ≃+* L) w₀ w h (algebraMap v.Completion w₀.Completion c) :=
    (Completion.continuous_congr _ w₀ w h).comp (NumberField.LiesOver.continuous_completionMap _ _)
  have hcont₂ : Continuous (algebraMap v.Completion w.Completion) :=
    (NumberField.LiesOver.continuous_completionMap _ _)
  have := Continuous.ext_on (denseRange_algebraMap_completion v) hcont₁ hcont₂ ?_
  · exact congrFun this c
  · rintro _ ⟨k, rfl⟩
    show Completion.congr (σ : L ≃+* L) w₀ w h
        (algebraMap v.Completion w₀.Completion (algebraMap K v.Completion k))
      = algebraMap v.Completion w.Completion (algebraMap K v.Completion k)
    rw [← IsScalarTower.algebraMap_apply K v.Completion w₀.Completion,
      ← IsScalarTower.algebraMap_apply K v.Completion w.Completion,
      IsScalarTower.algebraMap_apply K L w₀.Completion,
      IsScalarTower.algebraMap_apply K L w.Completion, Completion.congr_algebraMap]
    exact congrArg _ (σ.commutes k)

omit [NumberField L] in
/-- Transport of `Completion.congr` along an equality of source places. -/
theorem congr_index_congr {u u' : InfinitePlace L} (h : u = u') (w : InfinitePlace L)
    (f : L ≃+* L) (hf : ∀ y : L, w (f y) = u y) (hf' : ∀ y : L, w (f y) = u' y)
    (x : ∀ t : InfinitePlace L, t.Completion) :
    Completion.congr f u w hf (x u) = Completion.congr f u' w hf' (x u') := by
  subst h
  rfl

end Transport

section AdeleFixed

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem comap_eq_of_mem_stabilizer {σ : L ≃ₐ[K] L} {w : InfinitePlace L}
    (hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w) :
    w.comap ((σ : L ≃+* L) : L →+* L) = w :=
  Subtype.ext (AbsoluteValue.ext ((mem_stabilizer_iff_apply_eq w).1 hσ))

variable [IsGalois K L]

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- At a place `w` fixed by `σ`, the `w`-component of `σ • x` is the local action of `σ`. -/
theorem infiniteAdeleMap_apply_of_mem_stabilizer (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (σ : L ≃ₐ[K] L) (hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w)
    (x : InfiniteAdeleRing L) :
    infiniteAdeleMap (σ : L ≃+* L) x w = toLocalGal v w ⟨σ, hσ⟩ (x w) :=
  congr_index_congr (comap_eq_of_mem_stabilizer hσ) w (σ : L ≃+* L) (fun _ ↦ rfl)
    ((mem_stabilizer_iff_apply_eq w).1 hσ) (fun t ↦ x t)

variable {x : InfiniteAdeleRing L} (hx : ∀ σ : L ≃ₐ[K] L, infiniteAdeleMap (σ : L ≃+* L) x = x)

include hx

/-- The uniform preimage at an infinite place `v` of `K` of a `Gal(L/K)`-invariant infinite
adele of `L`. -/
theorem exists_uniform_preimage_infinite (v : InfinitePlace K) :
    ∃ c : v.Completion, ∀ (w : InfinitePlace L) [w.LiesOver v],
      algebraMap v.Completion w.Completion c = x w := by
  obtain ⟨w₀, hw₀⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  haveI inst₀ : w₀.LiesOver v := hw₀ ▸ (⟨rfl⟩ : w₀.LiesOver (w₀.comap (algebraMap K L)))
  have hfix : ∀ d : MulAction.stabilizer (L ≃ₐ[K] L) w₀, toLocalGal v w₀ d (x w₀) = x w₀ := by
    intro d
    rw [← infiniteAdeleMap_apply_of_mem_stabilizer v w₀ (d : L ≃ₐ[K] L) d.2 x, hx]
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_fixed v w₀ hfix
  refine ⟨c, ?_⟩
  intro w inst
  obtain ⟨σ, hσ⟩ := InfiniteAdeleRing.Fibre.exists_smul_eq
    (⟨w₀, LiesOver.comap_eq w₀ v⟩ : InfiniteAdeleRing.Fibre L v) ⟨w, LiesOver.comap_eq w v⟩
  have hσ' : σ • w₀ = w := congrArg Subtype.val hσ
  have h : ∀ y : L, w ((σ : L ≃+* L) y) = w₀ y := by
    intro y
    rw [← hσ']
    show w₀ ((σ⁻¹ : L ≃ₐ[K] L) ((σ : L ≃ₐ[K] L) y)) = w₀ y
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hcomap : w.comap ((σ : L ≃+* L) : L →+* L) = w₀ := Subtype.ext (AbsoluteValue.ext h)
  have hstep : Completion.congr (σ : L ≃+* L) w₀ w h (x w₀) = x w := by
    have hxw := congrFun (hx σ) w
    refine Eq.trans ?_ hxw
    exact (congr_index_congr hcomap w (σ : L ≃+* L) (fun _ ↦ rfl) h (fun t ↦ x t)).symm
  rw [← congr_algebraMap_completion v w₀ w σ h c, hc, hstep]

/-- The infinite adele of `K` underlying a `Gal(L/K)`-invariant infinite adele of `L`. -/
noncomputable def invInfiniteAdele : InfiniteAdeleRing K :=
  fun v ↦ (exists_uniform_preimage_infinite hx v).choose

theorem baseChange_invInfiniteAdele :
    InfiniteAdeleRing.baseChange (invInfiniteAdele hx) = x := by
  funext w
  rw [InfiniteAdeleRing.baseChange_apply]
  haveI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
  refine Eq.trans (completionMap_eq_algebraMap (w.comap (algebraMap K L)) w (fun _ ↦ rfl) _) ?_
  exact (exists_uniform_preimage_infinite hx (w.comap (algebraMap K L))).choose_spec w

/-- **`(𝔸_L^∞)^{Gal(L/K)} ⊆ 𝔸_K^∞`.** -/
theorem mem_range_infiniteAdeleBaseChange_of_fixed :
    x ∈ Set.range (InfiniteAdeleRing.baseChange (K := K) (L := L)) :=
  ⟨invInfiniteAdele hx, baseChange_invInfiniteAdele hx⟩

end AdeleFixed

end NumberField.InfinitePlace
