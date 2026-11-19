/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.CFT.SUnitDivisor

@[expose] public section

/-!
# Dirichlet's `S`-unit theorem: the `S`-units span the trace-zero hyperplane

Let `L` be a number field and `T` a finite set of finite places of `L`, and let
`S = SPlace L T` be the corresponding set of `S`-places (the archimedean places together with
`T`).  The logarithmic embedding sends the `S`-units into the trace-zero hyperplane
`(∏_{p ∈ S} ℝ)⁰` (`NumberField.sum_sLog_eq_zero`).  The main theorem of this file,
`NumberField.sUnitSpan_eq_sHyperplane`, is that its image **spans** that hyperplane:

`span ℝ { (log ‖x‖_p)_{p ∈ S} : x ∈ O_{L,S}^× } = { y : S → ℝ | ∑ y_p = 0 }.`

This is the `ℝ`-linear form of Dirichlet's `S`-unit theorem, and (together with the Galois
equivariance recorded below) it is the statement that `O_{L,S}^× ⊗ ℝ ≅ (∏_{w ∈ S} ℝ)⁰` as
`ℝ[Gal(L/K)]`-modules, which is the key input to the computation of the Herbrand quotient of
the `S`-unit group.

## Proof

No discreteness or Northcott-type finiteness is needed.  Write `V` for the span and project
`∏_{p ∈ S} ℝ` onto `(∏_{w ∈ T} ℝ) × logSpace L` (`NumberField.sProj`), where `logSpace L` is
Mathlib's target for the classical logarithmic embedding of `O_L^×`.  Then:

* the image of `V` contains `0 × logSpace L`, because the algebraic units are `S`-units whose
  finite coordinates vanish, and Mathlib's `unitLattice_span_eq_top` says their images span
  `logSpace L`;
* the image of `V` contains each `(e_w, 0)`, because the finiteness of the class group produces
  an `S`-unit whose divisor is `h · e_w` (`NumberField.exists_sDivisor_eq_classNumber_smul`).

Hence `sProj` maps `V` onto everything, so
`dim V ≥ #T + (r₁ + r₂ - 1) = #S - 1 = dim` of the hyperplane, and `V` is contained in the
hyperplane, so the two are equal.

## Main results

* `NumberField.sUnitSpan_eq_sHyperplane` : the span of the `S`-unit log image is the
  trace-zero hyperplane.
* `NumberField.finrank_sHyperplane` : the hyperplane has dimension `#S - 1`.
* `NumberField.sPerm_sLogVec`, `NumberField.map_sPerm_sUnitSpan`,
  `NumberField.map_sPerm_sHyperplane` : the whole picture is `Gal(L/K)`-equivariant when `T`
  is the set of places above a set `S` of places of the base field.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField.InfinitePlace
open scoped nonZeroDivisors NNReal

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

theorem adicAbv_eq_zpow (v : HeightOneSpectrum (𝓞 L)) {x : L} (hx : x ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv L v x
      = (Ideal.absNorm v.asIdeal : ℝ) ^ (- v.ord L x) := by
  have h0 : v.valuation L x ≠ 0 := IsDedekindDomain.HeightOneSpectrum.valuation_ne_zero hx
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ h0]
  push_cast
  congr 1
  rw [IsDedekindDomain.HeightOneSpectrum.ord, neg_neg]

variable {T : Set (HeightOneSpectrum (𝓞 L))}

/-- The logarithm of the normalised absolute value at a finite place, in terms of the order of
vanishing: `log ‖x‖_w = - ord_w(x) · log N(w)`. -/
theorem sLog_inr_eq_ord (w : T) (x : Lˣ) :
    sLog (Sum.inr w) x
      = - ((w : HeightOneSpectrum (𝓞 L)).ord L ((x : Lˣ) : L))
        * Real.log (Ideal.absNorm (w : HeightOneSpectrum (𝓞 L)).asIdeal) := by
  rw [sLog_inr, adicAbv_eq_zpow _ (Units.ne_zero x), Real.log_zpow]
  push_cast
  ring

theorem log_absNorm_pos (w : HeightOneSpectrum (𝓞 L)) :
    0 < Real.log (Ideal.absNorm w.asIdeal) := by
  refine Real.log_pos ?_
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w

/-- An algebraic unit has trivial normalised absolute value at every finite place. -/
theorem sLog_inr_unitsToSUnit (u : (𝓞 L)ˣ) (w : T) :
    sLog (Sum.inr w) ((Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u)) = 0 := by
  rw [sLog_inr_eq_ord]
  rw [show (((Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u : Lˣ)) : L)
      = algebraMap (𝓞 L) L (u : 𝓞 L) from rfl, ord_unit_eq_zero]
  ring

section Span

variable (L T)

variable [Fintype T]

/-- The sum-of-coordinates functional on `∏_{p ∈ S} ℝ`. -/
def sSum : (SPlace L T → ℝ) →ₗ[ℝ] ℝ := ∑ p : SPlace L T, LinearMap.proj p

@[simp]
theorem sSum_apply (y : SPlace L T → ℝ) : sSum L T y = ∑ p : SPlace L T, y p := by
  simp [sSum]

/-- The trace-zero hyperplane `(∏_{p ∈ S} ℝ)⁰`. -/
def sHyperplane : Submodule ℝ (SPlace L T → ℝ) := LinearMap.ker (sSum L T)

theorem mem_sHyperplane {y : SPlace L T → ℝ} :
    y ∈ sHyperplane L T ↔ ∑ p : SPlace L T, y p = 0 := by
  simp [sHyperplane, LinearMap.mem_ker]

/-- The `ℝ`-span of the image of the `S`-units under the logarithmic embedding. -/
def sUnitSpan : Submodule ℝ (SPlace L T → ℝ) :=
  Submodule.span ℝ (Set.range fun x : T.unit L ↦ (fun p ↦ sLog p ((x : Lˣ))))

theorem sUnitSpan_le_sHyperplane : sUnitSpan L T ≤ sHyperplane L T := by
  rw [sUnitSpan, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, mem_sHyperplane]
  exact sum_sLog_eq_zero x.2


/-- The logarithmic embedding vector of an element of `Lˣ`. -/
def sLogVec (x : Lˣ) : SPlace L T → ℝ := fun p ↦ sLog p x

variable {L T}

omit [Fintype T] in
theorem sLogVec_mem_sUnitSpan (x : T.unit L) : sLogVec L T (x : Lˣ) ∈ sUnitSpan L T :=
  Submodule.subset_span ⟨x, rfl⟩

variable (L T)

/-- The projection of `∏_{p ∈ S} ℝ` onto the finite coordinates and the archimedean
coordinates other than the distinguished one. -/
def sProj : (SPlace L T → ℝ) →ₗ[ℝ] ((T → ℝ) × NumberField.Units.dirichletUnitTheorem.logSpace L) :=
  LinearMap.prod (LinearMap.funLeft ℝ ℝ (Sum.inr : T → SPlace L T))
    (LinearMap.funLeft ℝ ℝ
      (fun w : {w : InfinitePlace L // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ↦
        (Sum.inl (w : InfinitePlace L) : SPlace L T)))

omit [Fintype T] in
@[simp]
theorem sProj_apply (y : SPlace L T → ℝ) :
    sProj L T y = (fun w : T ↦ y (Sum.inr w),
      fun w : {w : InfinitePlace L // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ↦ y (Sum.inl (w : InfinitePlace L)))
    := rfl

omit [Fintype T] in
/-- On an algebraic unit the projection is the classical logarithmic embedding. -/
theorem sProj_sLogVec_unit (u : (𝓞 L)ˣ) :
    sProj L T (sLogVec L T (Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u))
      = (0, NumberField.Units.logEmbedding L (Additive.ofMul u)) := by
  refine Prod.ext ?_ ?_
  · funext w
    exact sLog_inr_unitsToSUnit u w
  · funext w
    rw [sProj_apply]
    exact sLog_inl _ _

omit [Fintype T] in
open NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- Every vector supported on the archimedean coordinates alone, and lying in the image of the
classical logarithmic embedding's span, is in the image of the `S`-unit span. -/
theorem inr_mem_map_sProj (b : logSpace L) :
    ((0 : T → ℝ), b) ∈ (sUnitSpan L T).map (sProj L T) := by
  set Q := (sUnitSpan L T).map (sProj L T) with hQ
  set B : Submodule ℝ (logSpace L) :=
    Q.comap (LinearMap.inr ℝ (T → ℝ) (logSpace L)) with hB
  have hmem : ∀ u : (𝓞 L)ˣ, logEmbedding L (Additive.ofMul u) ∈ B := by
    intro u
    refine ⟨sLogVec L T ((Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u)), ?_, ?_⟩
    · exact sLogVec_mem_sUnitSpan
        ⟨Units.map (algebraMap (𝓞 L) L : (𝓞 L) →* L) u,
          (mem_unit_iff_ord _).2 fun w _ ↦ ord_unit_eq_zero _ _⟩
    · exact sProj_sLogVec_unit L T u
  have htop : (⊤ : Submodule ℝ (logSpace L)) ≤ B := by
    rw [← unitLattice_span_eq_top (K := L), Submodule.span_le]
    rintro y ⟨u, -, rfl⟩
    exact hmem (Additive.toMul u)
  exact htop trivial

open NumberField.Units NumberField.Units.dirichletUnitTheorem Classical in
/-- The finite-coordinate standard basis vectors are in the image of the `S`-unit span: this is
where the finiteness of the class group enters. -/
theorem single_mem_map_sProj (w₁ : T) :
    ((Pi.single w₁ 1 : T → ℝ), (0 : logSpace L)) ∈ (sUnitSpan L T).map (sProj L T) := by
  classical
  obtain ⟨x, hx⟩ := exists_sDivisor_eq_classNumber_smul (Set.toFinite T) (Pi.single w₁ 1 : T → ℤ)
  set k : ℝ := -(NumberField.classNumber L : ℝ) *
    Real.log (Ideal.absNorm (w₁ : HeightOneSpectrum (𝓞 L)).asIdeal) with hk
  have hk0 : k ≠ 0 := by
    refine mul_ne_zero ?_ (log_absNorm_pos _).ne'
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
    exact NumberField.classNumber_ne_zero L
  have hord : ∀ w : T, (w : HeightOneSpectrum (𝓞 L)).ord L (((x : Lˣ)) : L)
      = (NumberField.classNumber L : ℤ) * ((Pi.single w₁ 1 : T → ℤ) w) := by
    intro w
    have := congrFun hx w
    simpa using this
  have ha : (fun w : T ↦ sLog (Sum.inr w) ((x : Lˣ))) = k • (Pi.single w₁ 1 : T → ℝ) := by
    funext w
    rw [sLog_inr_eq_ord, hord w]
    by_cases hw : w = w₁
    · subst hw
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one, hk]
      push_cast
      ring
    · simp [Pi.single_eq_of_ne hw]
  have hmem1 : (sProj L T (sLogVec L T (x : Lˣ))) ∈ (sUnitSpan L T).map (sProj L T) :=
    ⟨_, sLogVec_mem_sUnitSpan x, rfl⟩
  have hmem2 : ((0 : T → ℝ),
      (fun w : {w : InfinitePlace L // w ≠ w₀} ↦ sLog (T := T) (Sum.inl (w : InfinitePlace L)) (x : Lˣ)))
      ∈ (sUnitSpan L T).map (sProj L T) := inr_mem_map_sProj L T _
  have hsub := Submodule.sub_mem _ hmem1 hmem2
  rw [sProj_apply] at hsub
  simp only [sLogVec] at hsub
  have heq : ((fun w : T ↦ sLog (Sum.inr w) ((x : Lˣ))),
      (fun w : {w : InfinitePlace L // w ≠ w₀} ↦ sLog (T := T) (Sum.inl (w : InfinitePlace L)) (x : Lˣ)))
      - ((0 : T → ℝ),
        (fun w : {w : InfinitePlace L // w ≠ w₀} ↦ sLog (T := T) (Sum.inl (w : InfinitePlace L)) (x : Lˣ)))
      = (k • (Pi.single w₁ 1 : T → ℝ), (0 : logSpace L)) := by
    rw [Prod.sub_def]
    refine Prod.ext ?_ ?_
    · simpa using ha
    · simp
  rw [heq] at hsub
  have := Submodule.smul_mem _ (k⁻¹) hsub
  rwa [Prod.smul_mk, smul_zero, smul_smul, inv_mul_cancel₀ hk0, one_smul] at this

open NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- **The projection of the `S`-unit span is everything.** -/
theorem map_sProj_sUnitSpan_eq_top : (sUnitSpan L T).map (sProj L T) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have h1 : ((a : T → ℝ), (0 : logSpace L)) ∈ (sUnitSpan L T).map (sProj L T) := by
    have hsum : ((a, 0) : (T → ℝ) × logSpace L)
        = ∑ w : T, a w • ((Pi.single w 1 : T → ℝ), (0 : logSpace L)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]
        simp only [Prod.smul_fst]
        rw [← Finset.univ_sum_single a]
        exact Finset.sum_congr rfl fun w _ ↦ by
          funext w'
          by_cases hw : w' = w
          · subst hw; simp
          · simp [Pi.single_eq_of_ne hw]
      · rw [Prod.snd_sum]
        simp
    rw [hsum]
    exact Submodule.sum_mem _ fun w _ ↦
      Submodule.smul_mem _ _ (single_mem_map_sProj L T w)
  have h2 := inr_mem_map_sProj L T b
  have h3 := Submodule.add_mem _ h1 h2
  simpa using h3

open Module NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem finrank_sHyperplane :
    finrank ℝ (sHyperplane L T) = Fintype.card (InfinitePlace L) + Fintype.card T - 1 := by
  classical
  have hsurj : Function.Surjective (sSum L T) := by
    intro c
    refine ⟨Pi.single (Sum.inl (Classical.arbitrary (InfinitePlace L))) c, ?_⟩
    rw [sSum_apply, Finset.sum_pi_single']
    simp
  have hrange : LinearMap.range (sSum L T) = ⊤ := LinearMap.range_eq_top.2 hsurj
  have h := LinearMap.finrank_range_add_finrank_ker (sSum L T)
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum] at h
  rw [sHyperplane]
  omega

open Module NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- **The `S`-units span the trace-zero hyperplane.**  This is the `ℝ`-linear form of
Dirichlet's `S`-unit theorem: the image of the `S`-unit group under the logarithmic embedding
spans exactly `(∏_{p ∈ S} ℝ)⁰`.  Because the logarithmic embedding is `Gal(L/K)`-equivariant
(`NumberField.sLogEmbedding_smul`), this identifies `O_{L,S}^× ⊗ ℝ` with `(∏_{w ∈ S} ℝ)⁰` as
`ℝ[Gal(L/K)]`-modules. -/
theorem sUnitSpan_eq_sHyperplane : sUnitSpan L T = sHyperplane L T := by
  classical
  refine Submodule.eq_of_le_of_finrank_le (sUnitSpan_le_sHyperplane L T) ?_
  have hle : finrank ℝ ((sUnitSpan L T).map (sProj L T)) ≤ finrank ℝ (sUnitSpan L T) :=
    Submodule.finrank_map_le _ _
  rw [map_sProj_sUnitSpan_eq_top, finrank_top, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, NumberField.Units.finrank_eq_rank] at hle
  rw [finrank_sHyperplane]
  have hpos : 1 ≤ Fintype.card (InfinitePlace L) := Fintype.card_pos
  rw [NumberField.Units.rank] at hle
  omega

/-! ## The Galois action on the hyperplane -/

section GaloisSpan

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype (placesOverSet K L S)]

/-- The permutation action of `Gal(L/K)` on `∏_{p ∈ S} ℝ`, coming from its action on the
`S`-places of `L`. -/
def sPerm (σ : L ≃ₐ[K] L) :
    (SPlace L (placesOverSet K L S) → ℝ) ≃ₗ[ℝ] (SPlace L (placesOverSet K L S) → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (MulAction.toPerm σ⁻¹)

omit [NumberField L] [NumberField K] [Fintype (placesOverSet K L S)] in
@[simp]
theorem sPerm_apply (σ : L ≃ₐ[K] L) (y : SPlace L (placesOverSet K L S) → ℝ)
    (p : SPlace L (placesOverSet K L S)) : sPerm L S σ y p = y (σ⁻¹ • p) := rfl

omit [Fintype (placesOverSet K L S)] in
/-- **The logarithmic embedding is `Gal(L/K)`-equivariant**, in vector form. -/
theorem sPerm_sLogVec (σ : L ≃ₐ[K] L) (x : Lˣ) :
    sPerm L S σ (sLogVec L (placesOverSet K L S) x)
      = sLogVec L (placesOverSet K L S) (σ • x) := by
  funext p
  rw [sPerm_apply, sLogVec, sLogVec]
  conv_rhs => rw [← smul_inv_smul σ p]
  exact (sLog_smul σ (σ⁻¹ • p) x).symm

omit [Fintype (placesOverSet K L S)] in
/-- **The `S`-unit span is a `Gal(L/K)`-submodule.** -/
theorem map_sPerm_sUnitSpan (σ : L ≃ₐ[K] L) :
    (sUnitSpan L (placesOverSet K L S)).map (sPerm L S σ).toLinearMap
      = sUnitSpan L (placesOverSet K L S) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap, sUnitSpan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine Submodule.mem_comap.2 ?_
    show sPerm L S σ (sLogVec L (placesOverSet K L S) ((x : Lˣ))) ∈ _
    rw [sPerm_sLogVec]
    exact sLogVec_mem_sUnitSpan (σ • x : SUnitGroup K L S)
  · rw [sUnitSpan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine ⟨sLogVec L (placesOverSet K L S) ((σ⁻¹ • x : SUnitGroup K L S) : Lˣ),
      sLogVec_mem_sUnitSpan _, ?_⟩
    show sPerm L S σ (sLogVec L (placesOverSet K L S)
        ((σ⁻¹ • x : SUnitGroup K L S) : Lˣ)) = sLogVec L (placesOverSet K L S) (x : Lˣ)
    rw [show ((σ⁻¹ • x : SUnitGroup K L S) : Lˣ) = σ⁻¹ • (x : Lˣ) from rfl,
      sPerm_sLogVec, smul_inv_smul]

/-- **The trace-zero hyperplane is a `Gal(L/K)`-submodule**, and it is the `S`-unit span. -/
theorem map_sPerm_sHyperplane (σ : L ≃ₐ[K] L) :
    (sHyperplane L (placesOverSet K L S)).map (sPerm L S σ).toLinearMap
      = sHyperplane L (placesOverSet K L S) := by
  rw [← sUnitSpan_eq_sHyperplane]
  exact map_sPerm_sUnitSpan L S σ

end GaloisSpan

end Span

end NumberField
