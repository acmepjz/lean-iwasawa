module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.RamificationInertia.Inertia

public import Iwasawalib.NumberTheory.CFT.AdicCompletionDecomposition
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

@[expose] public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField IntermediateField
open scoped WithZero IntermediateField NNReal

namespace NumberField

section Instances

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]


instance instNontriviallyNormedFieldAdicCompletion :
    NontriviallyNormedField (v.adicCompletion K) :=
  { (inferInstance : NormedField (v.adicCompletion K)) with
    non_trivial := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
      refine ⟨(((a : K) : v.adicCompletion K))⁻¹, ?_⟩
      have h1 : ‖((a : K) : v.adicCompletion K)‖ < 1 := by
        exact (FinitePlace.norm_lt_one_iff_mem (R := 𝓞 K) (K := K) (v := v) a).2 ha
      have h2 : ((a : K) : v.adicCompletion K) ≠ 0 := by
        simp only [ne_eq]
        rw [show ((a : K) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) (a : K) from rfl]
        simp [ha0, FaithfulSMul.algebraMap_eq_zero_iff]
      rw [norm_inv]
      rw [one_lt_inv_iff₀]
      exact ⟨by simpa [norm_pos_iff] using h2, h1⟩ }


end Instances

section Finite

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] adicCompletionComapAlgebra


/-- `L_w` is a topological `K_v`-module. -/
local instance continuousSMul_adicCompletion :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
  constructor
  have : (fun p : v.adicCompletion K × w.adicCompletion L ↦ p.1 • p.2) =
      fun p ↦ adicCompletionComap K L v w p.1 * p.2 := by
    funext p; exact Algebra.smul_def _ _
  rw [this]
  exact ((continuous_adicCompletionComap K L v w).comp continuous_fst).mul continuous_snd

/-- **`L_w` is spanned over `K_v` by the image of `L`.**  The `K_v`-span of the image of `L`
in `L_w` is a finite-dimensional, hence closed, subspace containing a dense set. -/
theorem span_range_algebraMap_eq_top :
    Submodule.span (v.adicCompletion K) (Set.range (algebraMap L (w.adicCompletion L))) = ⊤ := by
  classical
  set b := Module.finBasis K L with hb
  set S : Submodule (v.adicCompletion K) (w.adicCompletion L) :=
    Submodule.span _ (Set.range fun i ↦ algebraMap L (w.adicCompletion L) (b i)) with hS
  have hfin : Module.Finite (v.adicCompletion K) S :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  have hsub : Set.range (algebraMap L (w.adicCompletion L)) ⊆ (S : Set (w.adicCompletion L)) := by
    rintro _ ⟨y, rfl⟩
    have hy := b.sum_repr y
    rw [← hy, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul]
    have hc : algebraMap L (w.adicCompletion L) (algebraMap K L (b.repr y i))
        = algebraMap (v.adicCompletion K) (w.adicCompletion L)
            (algebraMap K (v.adicCompletion K) (b.repr y i)) :=
      (adicCompletionComap_algebraMap K L v w (b.repr y i)).symm
    rw [hc, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hclosed : IsClosed (S : Set (w.adicCompletion L)) := S.closed_of_finiteDimensional
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x ∈ closure (Set.range (algebraMap L (w.adicCompletion L))) :=
      (denseRange_algebraMap (R := 𝓞 L) (K := L) (v := w)) x
    exact hclosed.closure_subset_iff.2 hsub this
  refine eq_top_iff.2 ?_
  rw [← htop]
  exact Submodule.span_mono (Set.range_subset_iff.2 fun i ↦ ⟨b i, rfl⟩)

/-- **`L_w / K_v` is a finite extension.** -/
instance module_finite_adicCompletion :
    Module.Finite (v.adicCompletion K) (w.adicCompletion L) := by
  classical
  set b := Module.finBasis K L with hb
  refine ⟨⟨Finset.image (fun i ↦ algebraMap L (w.adicCompletion L) (b i)) Finset.univ, ?_⟩⟩
  rw [eq_top_iff, ← span_range_algebraMap_eq_top v w]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, rfl⟩
  have hy := b.sum_repr y
  rw [← hy, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul]
  have hc : algebraMap L (w.adicCompletion L) (algebraMap K L (b.repr y i))
      = algebraMap (v.adicCompletion K) (w.adicCompletion L)
          (algebraMap K (v.adicCompletion K) (b.repr y i)) :=
    (adicCompletionComap_algebraMap K L v w (b.repr y i)).symm
  rw [hc, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

end Finite

section Instances2

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] adicCompletionComapAlgebra

instance charZero_adicCompletion : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

local instance isScalarTower_adicCompletion :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun k ↦ by
    rw [IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
    exact (adicCompletionComap_algebraMap K L v w k).symm


end Instances2

section Normal

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] adicCompletionComapAlgebra isScalarTower_adicCompletion

/-- `L_w` is generated as a `K_v`-algebra by the image of `L`. -/
theorem adjoin_range_algebraMap_eq_top :
    Algebra.adjoin (v.adicCompletion K) (Set.range (algebraMap L (w.adicCompletion L))) = ⊤ := by
  have h : Submodule.span (v.adicCompletion K) (Set.range (algebraMap L (w.adicCompletion L)))
      ≤ Subalgebra.toSubmodule
        (Algebra.adjoin (v.adicCompletion K)
          (Set.range (algebraMap L (w.adicCompletion L)))) :=
    Submodule.span_le.2 Algebra.subset_adjoin
  refine eq_top_iff.2 fun x _ ↦ ?_
  exact h (by rw [span_range_algebraMap_eq_top]; trivial)

/-- If `α` generates `L` over `K`, then its image generates `L_w` over `K_v`. -/
theorem adjoin_singleton_eq_top {α : L} (hα : K⟮α⟯ = ⊤) :
    Algebra.adjoin (v.adicCompletion K) {algebraMap L (w.adicCompletion L) α} = ⊤ := by
  rw [eq_top_iff, ← adjoin_range_algebraMap_eq_top v w, Algebra.adjoin_le_iff]
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
      rw [← IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
        IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.adicCompletion L)]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

/-- The image of a primitive element is a root of the base-changed minimal polynomial. -/
theorem aeval_algebraMap_minpoly_map (α : L) :
    (Polynomial.aeval (algebraMap L (w.adicCompletion L) α))
      ((minpoly K α).map (algebraMap K (v.adicCompletion K))) = 0 := by
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
    minpoly.aeval, map_zero]

variable [IsGalois K L]

/-- `L_w` is a splitting field over `K_v` of the minimal polynomial of a primitive element
of `L / K`. -/
theorem isSplittingField_adicCompletion {α : L} (hα : K⟮α⟯ = ⊤) :
    Polynomial.IsSplittingField (v.adicCompletion K) (w.adicCompletion L)
      ((minpoly K α).map (algebraMap K (v.adicCompletion K))) where
  splits' := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq K L (w.adicCompletion L), ← Polynomial.map_map]
    exact (IsGalois.to_normal.splits α).map _
  adjoin_rootSet' := by
    have hne : (minpoly K α) ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite K α)
    have hmapne : ((minpoly K α).map (algebraMap K (v.adicCompletion K))).map
        (algebraMap (v.adicCompletion K) (w.adicCompletion L)) ≠ 0 := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      exact Polynomial.map_ne_zero hne
    have hroot : algebraMap L (w.adicCompletion L) α ∈
        ((minpoly K α).map (algebraMap K (v.adicCompletion K))).rootSet
          (w.adicCompletion L) :=
      Polynomial.mem_rootSet'.2 ⟨hmapne, aeval_algebraMap_minpoly_map v w α⟩
    refine eq_top_iff.2 ?_
    rw [← adjoin_singleton_eq_top v w hα]
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 hroot)

/-- **`L_w / K_v` is normal.** -/
instance normal_adicCompletion : Normal (v.adicCompletion K) (w.adicCompletion L) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  haveI := isSplittingField_adicCompletion v w hα
  exact Normal.of_isSplittingField ((minpoly K α).map (algebraMap K (v.adicCompletion K)))

/-- **`L_w / K_v` is a finite Galois extension.** -/
instance isGalois_adicCompletion : IsGalois (v.adicCompletion K) (w.adicCompletion L) where

end Normal

section Spectral

open WithZeroMulInt NumberField.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] adicCompletionComapAlgebra isScalarTower_adicCompletion

theorem toNNReal_pow_base {b : ℝ≥0} (hb : b ≠ 0) {n : ℕ} (hn : n ≠ 0) (x : ℤᵐ⁰) :
    (WithZeroMulInt.toNNReal hb x) ^ n = WithZeroMulInt.toNNReal (pow_ne_zero n hb) x := by
  by_cases hx : x = 0
  · rw [WithZeroMulInt.toNNReal_pos_apply hb hx, WithZeroMulInt.toNNReal_pos_apply _ hx,
      zero_pow hn]
  · have h1 : ∀ (c : ℝ≥0) (m : ℤ) (k : ℕ), (c ^ m) ^ k = c ^ (m * k) := by
      intro c m k; rw [← zpow_natCast (c ^ m) k, ← zpow_mul]
    have h2 : ∀ (c : ℝ≥0) (m : ℤ) (k : ℕ), (c ^ k) ^ m = c ^ ((k : ℤ) * m) := by
      intro c m k; rw [← zpow_natCast c k, ← zpow_mul]
    rw [WithZeroMulInt.toNNReal_neg_apply hb hx, WithZeroMulInt.toNNReal_neg_apply _ hx,
      h1, h2, mul_comm]

omit [NumberField K] in
/-- The ramification index of `w` over `v` is nonzero. -/
theorem ramificationIdx_ne_zero' : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot

/-- The base for the absolute value on `L_w` normalised so as to restrict to the canonical
absolute value of `K_v`: it is `N(v) ^ (1 / e(w|v))`. -/
def localBase : ℝ≥0 :=
  (Ideal.absNorm v.asIdeal : ℝ≥0) ^ ((v.asIdeal.ramificationIdx' w.asIdeal : ℝ)⁻¹)

theorem one_lt_localBase : (1 : ℝ≥0) < localBase v w := by
  unfold localBase
  refine NNReal.one_lt_rpow (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) ?_
  refine inv_pos.2 ?_
  exact_mod_cast Nat.pos_of_ne_zero (ramificationIdx_ne_zero' v w)

theorem localBase_ne_zero : localBase v w ≠ 0 := ne_zero_of_lt (one_lt_localBase v w)

theorem localBase_pow :
    (localBase v w) ^ (v.asIdeal.ramificationIdx' w.asIdeal) = (Ideal.absNorm v.asIdeal : ℝ≥0) := by
  unfold localBase
  rw [← NNReal.rpow_natCast _ (v.asIdeal.ramificationIdx' w.asIdeal), ← NNReal.rpow_mul,
    inv_mul_cancel₀ (by exact_mod_cast ramificationIdx_ne_zero' v w), NNReal.rpow_one]

theorem toNNReal_congr_base {b c : ℝ≥0} (hb : b ≠ 0) (hc : c ≠ 0) (h : b = c) (x : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal hb x = WithZeroMulInt.toNNReal hc x := by subst h; rfl

/-- The absolute value on `L_w` normalised so that it restricts to the canonical absolute value
of `K_v` along the local base change map. -/
def localAbv : AbsoluteValue (w.adicCompletion L) ℝ where
  toFun x := (WithZeroMulInt.toNNReal (localBase_ne_zero v w) (Valued.v x) : ℝ)
  map_mul' x y := by push_cast [map_mul]; ring
  nonneg' x := (WithZeroMulInt.toNNReal _ (Valued.v x)).coe_nonneg
  eq_zero' x := by
    simp only [NNReal.coe_eq_zero, map_eq_zero]
  add_le' x y := by
    have hmono := (WithZeroMulInt.toNNReal_strictMono (one_lt_localBase v w)).monotone
    have h := hmono ((Valued.v (R := w.adicCompletion L)).map_add x y)
    have h' : (WithZeroMulInt.toNNReal (localBase_ne_zero v w) (Valued.v (x + y)) : ℝ)
        ≤ max (WithZeroMulInt.toNNReal (localBase_ne_zero v w) (Valued.v x) : ℝ)
          (WithZeroMulInt.toNNReal (localBase_ne_zero v w) (Valued.v y) : ℝ) := by
      rw [← NNReal.coe_max]
      exact_mod_cast h.trans_eq (by rw [Monotone.map_max hmono])
    refine h'.trans (max_le ?_ ?_)
    · simp
    · simp

theorem localAbv_apply (x : w.adicCompletion L) :
    localAbv v w x = (WithZeroMulInt.toNNReal (localBase_ne_zero v w) (Valued.v x) : ℝ) :=
  rfl

/-- The normalised absolute value on `L_w` restricts to the canonical norm of `K_v`. -/
theorem localAbv_algebraMap (c : v.adicCompletion K) :
    localAbv v w (algebraMap (v.adicCompletion K) (w.adicCompletion L) c) = ‖c‖ := by
  rw [localAbv_apply]
  have hc : (algebraMap (v.adicCompletion K) (w.adicCompletion L) c)
      = adicCompletionComap K L v w c := rfl
  rw [hc, valued_adicCompletionComap, map_pow,
    toNNReal_pow_base _ (ramificationIdx_ne_zero' v w),
    toNNReal_congr_base _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (localBase_pow v w),
    ← NumberField.FinitePlace.norm_def]

end Spectral

section LocalGal

open WithZeroMulInt

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] adicCompletionComapAlgebra isScalarTower_adicCompletion

/-- **Every `K_v`-automorphism of `L_w` preserves the `w`-adic valuation.**  This is the
uniqueness of the extension of a complete nonarchimedean absolute value, via the spectral
norm. -/
theorem valued_algEquiv
    (τ : (w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L))
    (x : w.adicCompletion L) : (Valued.v (τ x) : ℤᵐ⁰) = Valued.v x := by
  have h1 : ∀ y : w.adicCompletion L,
      localAbv v w y = spectralNorm (v.adicCompletion K) (w.adicCompletion L) y := fun y ↦
    spectralNorm_unique_field_norm_ext (localAbv_algebraMap v w) y
  have h3 : localAbv v w (τ x) = localAbv v w x := by
    rw [h1, h1, spectralNorm_eq_of_equiv τ x]
  rw [localAbv_apply, localAbv_apply] at h3
  have h4 : WithZeroMulInt.toNNReal (localBase_ne_zero v w) (Valued.v (τ x))
      = WithZeroMulInt.toNNReal (localBase_ne_zero v w) (Valued.v x) := by
    exact_mod_cast h3
  exact (WithZeroMulInt.toNNReal_strictMono (one_lt_localBase v w)).injective h4

omit [NumberField K] [w.asIdeal.LiesOver v.asIdeal] in
/-- An automorphism of `L` that preserves the `w`-adic valuation fixes the place `w`. -/
theorem smul_eq_of_valuation_eq {σ : L ≃ₐ[K] L}
    (h : ∀ x : L, w.valuation L (σ x) = w.valuation L x) : σ • w = w := by
  have hval : ∀ y : L, (σ • w).valuation L y = w.valuation L y := by
    intro y
    have h1 := valuation_smul_heightOneSpectrum σ w (σ.symm y)
    rw [AlgEquiv.apply_symm_apply] at h1
    rw [h1, ← h (σ.symm y), AlgEquiv.apply_symm_apply]
  refine HeightOneSpectrum.ext (Ideal.ext fun a ↦ ?_)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) (σ • w) a,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w a, hval]

variable [IsGalois K L]

/-- **The decomposition group maps to `Gal(L_w/K_v)`.**  An element of `D_w` acts on `L_w`
by a `K_v`-algebra automorphism. -/
def toLocalGal (d : decompositionGroup K L w) :
    (w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L) :=
  { decompositionRingAut K L w d with
    commutes' := fun c ↦ decomposition_smul_adicCompletionComap v w d c }

omit [IsGalois K L] in
@[simp]
theorem toLocalGal_coe (d : decompositionGroup K L w) (x : L) :
    toLocalGal v w d ((x : L) : w.adicCompletion L)
      = (((d : L ≃ₐ[K] L) x : L) : w.adicCompletion L) :=
  decompositionRingAut_coe w d x

/-- **The restriction of a `K_v`-automorphism of `L_w` to `L`.** -/
def restrictLocal (τ : (w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)) :
    L ≃ₐ[K] L :=
  AlgEquiv.restrictNormalHom L (τ.restrictScalars K)

theorem algebraMap_restrictLocal
    (τ : (w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)) (x : L) :
    algebraMap L (w.adicCompletion L) (restrictLocal v w τ x)
      = τ (algebraMap L (w.adicCompletion L) x) :=
  AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L x

/-- The restriction of a `K_v`-automorphism of `L_w` lies in the decomposition group. -/
theorem restrictLocal_mem_decompositionGroup
    (τ : (w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)) :
    restrictLocal v w τ ∈ decompositionGroup K L w := by
  refine smul_eq_of_valuation_eq w (fun x ↦ ?_)
  have h1 : (Valued.v ((restrictLocal v w τ x : L) : w.adicCompletion L) : ℤᵐ⁰)
      = Valued.v ((x : L) : w.adicCompletion L) := by
    rw [show (((restrictLocal v w τ x : L)) : w.adicCompletion L)
        = algebraMap L (w.adicCompletion L) (restrictLocal v w τ x) from rfl,
      algebraMap_restrictLocal]
    exact valued_algEquiv v w τ _
  rwa [adicCompletion.valued_coe, adicCompletion.valued_coe] at h1

theorem restrictLocal_toLocalGal (d : decompositionGroup K L w) :
    restrictLocal v w (toLocalGal v w d) = (d : L ≃ₐ[K] L) := by
  refine AlgEquiv.ext fun x ↦ (algebraMap L (w.adicCompletion L)).injective ?_
  rw [algebraMap_restrictLocal]
  exact toLocalGal_coe v w d x

theorem toLocalGal_restrictLocal
    (τ : (w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)) :
    toLocalGal v w ⟨restrictLocal v w τ, restrictLocal_mem_decompositionGroup v w τ⟩ = τ := by
  have h : (toLocalGal v w
      ⟨restrictLocal v w τ, restrictLocal_mem_decompositionGroup v w τ⟩ :
        (w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)).toAlgHom
      = τ.toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (adjoin_range_algebraMap_eq_top v w) ?_
    rintro _ ⟨x, rfl⟩
    show toLocalGal v w ⟨restrictLocal v w τ, restrictLocal_mem_decompositionGroup v w τ⟩
        (algebraMap L (w.adicCompletion L) x) = τ (algebraMap L (w.adicCompletion L) x)
    rw [← algebraMap_restrictLocal v w τ x]
    exact toLocalGal_coe v w _ x
  exact AlgEquiv.ext fun x ↦ AlgHom.congr_fun h x

/-- **`D_w ≃ Gal(L_w/K_v)`.**  For a finite Galois extension of number fields, the
decomposition group of a finite place `w` of `L` over `v` is isomorphic to the Galois group of
the local extension `L_w / K_v`. -/
def decompositionGroupEquivLocalGal :
    decompositionGroup K L w ≃*
      ((w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)) where
  toFun := toLocalGal v w
  invFun τ := ⟨restrictLocal v w τ, restrictLocal_mem_decompositionGroup v w τ⟩
  left_inv d := Subtype.ext (restrictLocal_toLocalGal v w d)
  right_inv τ := toLocalGal_restrictLocal v w τ
  map_mul' d d' := by
    refine AlgEquiv.ext fun x ↦ ?_
    show decompositionRingAut K L w (d * d') x = _
    rw [map_mul]
    rfl

@[simp]
theorem decompositionGroupEquivLocalGal_apply (d : decompositionGroup K L w) :
    decompositionGroupEquivLocalGal v w d = toLocalGal v w d := rfl

/-- The map `D_w → Aut(L_w)` is injective. -/
theorem toLocalGal_injective : Function.Injective (toLocalGal v w) :=
  (decompositionGroupEquivLocalGal v w).injective

/-- The map `D_w → Gal(L_w/K_v)` is surjective. -/
theorem toLocalGal_surjective : Function.Surjective (toLocalGal v w) :=
  (decompositionGroupEquivLocalGal v w).surjective

/-- **`L_w^{D_w} = K_v`.**  An element of `L_w` fixed by the decomposition group lies in the
image of the local base change map. -/
theorem mem_range_adicCompletionComap_of_fixed {x : w.adicCompletion L}
    (hx : ∀ d : decompositionGroup K L w, d • x = x) :
    x ∈ (adicCompletionComap K L v w).range := by
  have h : x ∈ Set.range (algebraMap (v.adicCompletion K) (w.adicCompletion L)) := by
    refine (IsGalois.mem_range_algebraMap_iff_fixed x).2 fun f ↦ ?_
    obtain ⟨d, rfl⟩ := toLocalGal_surjective v w f
    exact hx d
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc⟩

/-- **`L_w^{D_w} = K_v`**, as an equality of subrings of `L_w`. -/
theorem fixedPoints_decompositionGroup_eq_range :
    FixedPoints.subring (w.adicCompletion L) (decompositionGroup K L w)
      = (adicCompletionComap K L v w).range := by
  refine le_antisymm (fun x hx ↦ mem_range_adicCompletionComap_of_fixed v w hx) ?_
  exact range_adicCompletionComap_le_fixedPoints v w

/-- The local degree `[L_w : K_v]` is the order of the decomposition group. -/
theorem finrank_adicCompletion :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L)
      = Nat.card (decompositionGroup K L w) :=
  (IsGalois.card_aut_eq_finrank (v.adicCompletion K) (w.adicCompletion L)).symm.trans
    (Nat.card_congr (decompositionGroupEquivLocalGal v w).toEquiv).symm

/-! ### The local degree is `e · f` -/

section Degree

open scoped Pointwise

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem decompositionGroup_eq_stabilizer :
    decompositionGroup K L w = MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  ext σ
  rw [mem_decompositionGroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    rw [← HeightOneSpectrum.smul_asIdeal, h]
  · intro h
    exact HeightOneSpectrum.ext (by rw [HeightOneSpectrum.smul_asIdeal, h])

/-- **The local degree.**  For a finite Galois extension of number fields,
`[L_w : K_v] = e(w|v) · f(w|v)`. -/
theorem finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L)
      = v.asIdeal.ramificationIdx' w.asIdeal * v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  rw [finrank_adicCompletion v w, decompositionGroup_eq_stabilizer (K := K) w,
    Ideal.card_stabilizer_eq (G := L ≃ₐ[K] L) v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.asIdeal]

end Degree

end LocalGal

section AdeleFixed

open IsDedekindDomain.FiniteAdeleRing

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable {a : FiniteAdeleRing (𝓞 L) L} (ha : ∀ σ : L ≃ₐ[K] L, σ • a = a)

omit ha [NumberField K] [NumberField L] [IsGalois K L] in
theorem liesOver_of_under_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (h : w.under (𝓞 K) = v) : w.asIdeal.LiesOver v.asIdeal :=
  h ▸ liesOver_under (A := 𝓞 K) w

include ha

/-- Each local component of a `Gal(L/K)`-invariant finite adele of `L` comes from the
completion of `K` at the place below. -/
theorem exists_comap_eq_component (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    ∃ c : v.adicCompletion K, adicCompletionComap K L v w c = a w := by
  have hfix : ∀ d : decompositionGroup K L w, d • (a w) = a w := by
    intro d
    rw [← finiteAdele_smul_apply_of_mem_decompositionGroup d a, ha]
  exact mem_range_adicCompletionComap_of_fixed v w hfix

omit [IsGalois K L] in
/-- Transporting a local preimage along the Galois action. -/
theorem comap_smul_eq_component (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (inst : (σ • w).asIdeal.LiesOver v.asIdeal) (c : v.adicCompletion K)
    (hc : adicCompletionComap K L v w c = a w) :
    adicCompletionComap K L v (σ • w) c = a (σ • w) := by
  haveI := inst
  rw [← adicCompletionCongr_adicCompletionComap K L (σ : L ≃+* L) (fun k ↦ σ.commutes k) v w
    (σ • w) (valuation_smul_heightOneSpectrum σ w) c, hc,
    show adicCompletionCongr (σ : L ≃+* L) w (σ • w) (valuation_smul_heightOneSpectrum σ w)
      = adicCompletionSmulEquiv σ w from rfl,
    ← finiteAdele_smul_apply_smul σ a w, ha σ]

/-- The uniform local preimage at a place `v` of `K`: one element of `K_v` that maps to the
component of `a` at *every* place of `L` above `v`. -/
theorem exists_uniform_comap (v : HeightOneSpectrum (𝓞 K)) :
    ∃ c : v.adicCompletion K, ∀ (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal],
      adicCompletionComap K L v w c = a w := by
  obtain ⟨w₀, hw₀⟩ := IsDedekindDomain.HeightOneSpectrum.exists_under_eq (B := 𝓞 L) v
  haveI inst₀ : w₀.asIdeal.LiesOver v.asIdeal := liesOver_of_under_eq hw₀
  obtain ⟨c, hc⟩ := exists_comap_eq_component ha v w₀
  refine ⟨c, ?_⟩
  intro w inst
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_under_eq w₀ w (inst₀.over.symm.trans inst.over)
  subst hσ
  exact comap_smul_eq_component ha v w₀ σ inst c hc

/-- The `v`-component of the finite adele of `K` underlying a Galois-invariant finite adele
of `L`. -/
noncomputable def invComponent (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  (exists_uniform_comap ha v).choose

theorem comap_invComponent (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    adicCompletionComap K L v w (invComponent ha v) = a w :=
  (exists_uniform_comap ha v).choose_spec w

theorem invComponent_mem_integers (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (h : a w ∈ w.adicCompletionIntegers L) :
    invComponent ha v ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers] at h ⊢
  rw [← comap_invComponent ha v w, valued_adicCompletionComap] at h
  by_contra hcon
  exact absurd h (not_le.2 (one_lt_pow₀ (not_le.1 hcon) (ramificationIdx_ne_zero' v w)))

/-- The finite adele of `K` underlying a `Gal(L/K)`-invariant finite adele of `L`. -/
noncomputable def invAdele : FiniteAdeleRing (𝓞 K) K :=
  ⟨fun v ↦ invComponent ha v, by
    rw [Filter.eventually_cofinite]
    have hfin : {w : HeightOneSpectrum (𝓞 L) | a w ∉ w.adicCompletionIntegers L}.Finite := by
      have h2 := a.2
      rw [Filter.eventually_cofinite] at h2
      exact h2
    refine Set.Finite.subset (hfin.image (fun w ↦ w.under (𝓞 K))) ?_
    intro v hv
    obtain ⟨w, hw⟩ := IsDedekindDomain.HeightOneSpectrum.exists_under_eq (B := 𝓞 L) v
    haveI := liesOver_of_under_eq hw
    exact ⟨w, fun hmem ↦ hv (invComponent_mem_integers ha v w hmem), hw⟩⟩

theorem finiteAdeleBaseChange_invAdele : finiteAdeleBaseChange K L (invAdele ha) = a := by
  refine FiniteAdeleRing.ext L fun w ↦ ?_
  rw [baseChange_apply]
  exact comap_invComponent ha (w.under (𝓞 K)) w

/-- **`(𝔸_L^f)^{Gal(L/K)} ⊆ 𝔸_K^f`.** -/
theorem mem_range_finiteAdeleBaseChange_of_fixed :
    a ∈ (finiteAdeleBaseChange K L).range :=
  ⟨invAdele ha, finiteAdeleBaseChange_invAdele ha⟩

end AdeleFixed

section AdeleFixedTop

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **`(𝔸_L^f)^{Gal(L/K)} = 𝔸_K^f`.**  For a finite Galois extension of number fields, the
subring of `Gal(L/K)`-invariants of the finite adele ring of `L` is exactly the image of the
finite adele ring of `K`. -/
theorem fixedPoints_finiteAdele_eq_range :
    FixedPoints.subring (FiniteAdeleRing (𝓞 L) L) (L ≃ₐ[K] L)
      = (finiteAdeleBaseChange K L).range :=
  le_antisymm (fun _ hx ↦ mem_range_finiteAdeleBaseChange_of_fixed hx)
    (range_finiteAdeleBaseChange_le_fixedPoints K L)

end AdeleFixedTop

end NumberField
