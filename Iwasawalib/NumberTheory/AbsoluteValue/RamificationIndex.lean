/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Iwasawalib.NumberTheory.AbsoluteValue.GelfandTornheim
public import Iwasawalib.NumberTheory.AbsoluteValue.InertiaSubgroup
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Iwasawalib.Topology.Algebra.Group.Basic

@[expose] public section

/-!

# Ramification index for a place (`AbsoluteValue`)

(To be written)

References:

- [J. W. S. Cassels, A. Frohlich, editors, *Algebraic Number Theory*][cassels1967algebraic]

-/

namespace AbsoluteValue

/-! ### TODO: go mathlib -/

/-- TODO: go mathlib -/
theorem _root_.IntermediateField.restrictRestrictAlgEquivMapHom_injective_of_tower_top
    (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L]
    [IsScalarTower F K L] [Normal F L] :
    Function.Injective (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  ext x
  replace ha := congr($(ha) x)
  simpa [IntermediateField.restrictRestrictAlgEquivMapHom] using ha

/-- TODO: go mathlib -/
@[simp]
theorem _root_.AlgEquiv.algebraMap_restrictNormalHom_apply
    {F : Type*} [Field F] {K₁ : Type*} [Field K₁] [Algebra F K₁] (E : Type*) [Field E] [Algebra F E]
    [Algebra E K₁] [IsScalarTower F E K₁] [Normal F E] (φ : Gal(K₁/F)) (x : E) :
    algebraMap E K₁ (AlgEquiv.restrictNormalHom E φ x) = φ (algebraMap E K₁ x) := by
  simp [AlgEquiv.restrictNormalHom]

/-- TODO: go mathlib -/
@[simp]
theorem _root_.IntermediateField.alrebraMap_restrictRestrictAlgEquivMapHom_apply
    (F K L E : Type*) [Field F] [Field K] [Field L] [Field E] [Algebra F K] [Algebra F L]
    [Algebra F E] [Algebra K E] [Algebra L E] [IsScalarTower F K E] [IsScalarTower F L E]
    [Normal F K] (φ : Gal(E/L)) (x : K) :
    algebraMap K E (IntermediateField.restrictRestrictAlgEquivMapHom F K L E φ x) =
      φ (algebraMap K E x) := by
  simp [IntermediateField.restrictRestrictAlgEquivMapHom]

/-- TODO: go mathlib -/
theorem _root_.IntermediateField.restrictRestrictAlgEquivMapHom_comp_restrictRestrictAlgEquivMapHom
    (F K F' K' F'' K'' : Type*) [Field F] [Field K] [Field F'] [Field K'] [Field F''] [Field K'']
    [Algebra F K] [Algebra F' K'] [Algebra F'' K''] [Algebra F F'] [Algebra F' F''] [Algebra F F'']
    [Algebra F K'] [Algebra F' K''] [Algebra F K''] [Algebra K K'] [Algebra K' K''] [Algebra K K'']
    [IsScalarTower F K K'] [IsScalarTower F' K' K''] [IsScalarTower F F' K'] [IsScalarTower F K K'']
    [IsScalarTower F F'' K''] [IsScalarTower F' F'' K''] [IsScalarTower K K' K'']
    [Normal F K] [Normal F' K'] :
    (IntermediateField.restrictRestrictAlgEquivMapHom F K F' K').comp
      (IntermediateField.restrictRestrictAlgEquivMapHom F' K' F'' K'') =
        IntermediateField.restrictRestrictAlgEquivMapHom F K F'' K'' := by
  ext a x
  apply_fun _ using (algebraMap K K'').injective
  convert Eq.refl (a (algebraMap K K'' x))
  · simp [IsScalarTower.algebraMap_apply K K' K'']
  · simp

/-! ### Ramification index of a place for an extension -/

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then the
ramification index of `v` for `K / F` is defined to be the index of `Iᵥ(L/K)` in `Iᵥ(L/F)`
(`0` means infinite). Later we will show that this depends only on the place of `K` below `v`
(`AbsoluteValue.ramificationIdxOfIsScalarTower_eq_of_comp_eq`),
and is independent of the choice of `L` (`AbsoluteValue.ramificationIdx_spec`). -/
noncomputable def ramificationIdxOfIsScalarTower
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) : ℕ :=
    ((v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L)).relIndex (v.inertiaSubgroup F)

/-- The ramification index of `v` for `K / F` is equal to `[Iᵥ(L/F) ⊓ Gal(L/K) : Iᵥ(L/F)]`,
since `Iᵥ(L/K) = Iᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem ramificationIdxOfIsScalarTower_eq_range_relIndex
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.ramificationIdxOfIsScalarTower F K =
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L).range.relIndex
        (v.inertiaSubgroup F) := by
  rw [ramificationIdxOfIsScalarTower, v.inertiaSubgroup_eq_comap F K, Subgroup.map_comap_eq,
    Subgroup.inf_relIndex_right]

/-- A place of `L` and its restriction to `L'` by an isomorphism `L' ≃ₐ[K] L` have the same
ramification index for `K / F`. -/
theorem ramificationIdxOfIsScalarTower_comp_algEquiv_eq
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    {L' : Type*} [Field L'] [Algebra F L'] [Algebra K L'] [IsScalarTower F K L'] [Normal F L']
    (v : AbsoluteValue L ℝ) (σ : L' ≃ₐ[K] L) :
    (v.comp (f := (σ : L' →+* L)) σ.injective).ramificationIdxOfIsScalarTower F K =
      v.ramificationIdxOfIsScalarTower F K := by
  simp only [ramificationIdxOfIsScalarTower_eq_range_relIndex]
  rw [v.inertiaSubgroup_comp_algEquiv_eq_comap (σ.restrictScalars F),
    Subgroup.comap_equiv_eq_map_symm]
  convert Subgroup.relIndex_map_map_of_injective
    (f := ((σ.restrictScalars F).autCongr.symm : Gal(L/F) →* Gal(L'/F))) _ _ (MulEquiv.injective _)
  rw [← Subgroup.comap_equiv_eq_map_symm]
  ext τ
  simp only [MonoidHom.mem_range, Subgroup.mem_comap, MonoidHom.coe_coe, AlgEquiv.autCongr_apply]
  refine ⟨fun ⟨x, h⟩ ↦ ⟨σ.autCongr x, ?_⟩, fun ⟨x, h⟩ ↦ ⟨σ.autCongr.symm x, ?_⟩⟩
  · ext a
    simpa [IntermediateField.restrictRestrictAlgEquivMapHom] using congr($h (σ.symm a))
  · ext a
    simpa [IntermediateField.restrictRestrictAlgEquivMapHom] using congr(σ.symm ($h (σ a)))

/-- A generalization of `AbsoluteValue.ramificationIdxOfIsScalarTower_comp_algEquiv_eq`. -/
theorem ramificationIdxOfIsScalarTower_comp_ringEquiv_eq
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    {F' K' : Type*} [Field F'] [Field K'] [Algebra F' K']
    {L' : Type*} [Field L'] [Algebra F' L'] [Algebra K' L'] [IsScalarTower F' K' L'] [Normal F' L']
    (v : AbsoluteValue L ℝ) (e : F' ≃+* F) (f : K' ≃+* K) (g : L' ≃+* L)
    (hcomp0 : (algebraMap F K).comp e = RingHom.comp f (algebraMap F' K'))
    (hcomp : (algebraMap K L).comp f = RingHom.comp g (algebraMap K' L')) :
    (v.comp (f := (g : L' →+* L)) g.injective).ramificationIdxOfIsScalarTower F' K' =
      v.ramificationIdxOfIsScalarTower F K := by
  simp only [ramificationIdxOfIsScalarTower_eq_range_relIndex]
  have hcomp1 : (algebraMap F L).comp e = RingHom.comp g (algebraMap F' L') := by
    ext x
    simpa [← IsScalarTower.algebraMap_apply] using congr($(hcomp) (f.symm ($(hcomp0) x)))
  rw [v.inertiaSubgroup_comp_ringEquiv_eq_comap e.surjective hcomp1,
    Subgroup.comap_equiv_eq_map_symm]
  convert Subgroup.relIndex_map_map_of_injective
    (f := ((AlgEquiv.autCongrOfSurjective e.surjective hcomp1).symm : Gal(L/F) →* Gal(L'/F')))
    _ _ (MulEquiv.injective _)
  rw [← Subgroup.comap_equiv_eq_map_symm]
  ext τ
  simp only [MonoidHom.mem_range, Subgroup.mem_comap, MonoidHom.coe_coe]
  refine ⟨fun ⟨x, h⟩ ↦ ⟨AlgEquiv.autCongrOfSurjective f.surjective hcomp x, ?_⟩,
    fun ⟨x, h⟩ ↦ ⟨(AlgEquiv.autCongrOfSurjective f.surjective hcomp).symm x, ?_⟩⟩
  · ext a
    simpa [IntermediateField.restrictRestrictAlgEquivMapHom] using congr($h (g.symm a))
  · ext a
    simpa [IntermediateField.restrictRestrictAlgEquivMapHom] using congr(g.symm ($h (g a)))

/-- Any two places of `L` which are the same when restricted to `K` have the same
ramification index for `K / F` (since they are conjugate). -/
theorem ramificationIdxOfIsScalarTower_eq_of_comp_eq
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    {v w : AbsoluteValue L ℝ}
    (h : v.comp (algebraMap K L).injective = w.comp (algebraMap K L).injective) :
    v.ramificationIdxOfIsScalarTower F K = w.ramificationIdxOfIsScalarTower F K := by
  have := Normal.tower_top_of_normal F K L
  obtain ⟨σ, h⟩ := exists_algEquiv_comp_eq_of_comp_eq h.symm
  simpa only [h] using ramificationIdxOfIsScalarTower_comp_algEquiv_eq F K w σ

open Subgroup in
/-- TODO: go mathlib -/
@[to_additive]
theorem _root_.Subgroup.relIndex_map_map_of_ker_inf_le
    {G G' : Type*} [Group G] [Group G'] {f : G →* G'} (H K : Subgroup G)
    (hle : H ≤ K) (hf : f.ker ⊓ K ≤ H) :
    (Subgroup.map f H).relIndex (Subgroup.map f K) = H.relIndex K := by
  rw [← relIndex_comap, comap_map_eq, ← inf_relIndex_right H K, ← inf_relIndex_right (H ⊔ f.ker) K]
  congr 1
  refine le_antisymm ?_ (by simp)
  simp only [le_inf_iff, inf_le_right, and_true]
  intro x h
  rw [mem_inf, mem_sup_of_normal_right] at h
  obtain ⟨⟨y, hy, z, hz, rfl⟩, hx⟩ := h
  have := mul_mem (inv_mem (hle hy)) hx
  rw [← mul_assoc, inv_mul_cancel, one_mul] at this
  exact mul_mem hy (hf ⟨hz, this⟩)

open IntermediateField in
/-- TODO: go mathlib -/
theorem _root_.AlgEquiv.restrictNormalHom_ker_eq_range
    {F : Type*} [Field F] {K₁ : Type*} [Field K₁] [Algebra F K₁] (E : Type*)
    [Field E] [Algebra F E] [Algebra E K₁] [IsScalarTower F E K₁] [Normal F E] [Normal F K₁] :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := K₁) E).ker =
      (restrictRestrictAlgEquivMapHom F K₁ E K₁).range := by
  ext σ
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  refine ⟨fun h ↦ ?_, fun ⟨τ, h⟩ ↦ ?_⟩
  · let τ : Gal(K₁/E) := {
      toRingEquiv := σ
      commutes' r := by simpa using congr(algebraMap E K₁ ($h r))
    }
    use τ
    ext x
    simp [restrictRestrictAlgEquivMapHom, τ]
  · rw [← h]
    ext x
    apply_fun _ using (algebraMap E K₁).injective
    simp only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, AlgEquiv.restrictNormal_commutes]
    simp [IntermediateField.restrictRestrictAlgEquivMapHom]

open AlgEquiv IntermediateField in
/-- If `M / L / K / F` is an extension tower, `M / F` and `L / F` are Galois, `v` is a place of `L`,
`w` is a place of `M` above `v`, then `v` and `w` have the same ramification index for `K / F`. -/
theorem ramificationIdxOfIsScalarTower_eq_of_liesOver
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    {M : Type*} [Field M] [Algebra F M] [Algebra K M] [Algebra L M]
    [IsScalarTower F K M] [IsScalarTower F L M] [IsScalarTower K L M] [Normal F M]
    (v : AbsoluteValue L ℝ) (w : AbsoluteValue M ℝ) [w.LiesOver v] :
    v.ramificationIdxOfIsScalarTower F K = w.ramificationIdxOfIsScalarTower F K := by
  simp only [ramificationIdxOfIsScalarTower, inertiaSubgroup_eq_comap F K, Subgroup.map_comap_eq,
    ← map_inertiaSubgroup_eq_of_liesOver F v w]
  have h1 : (restrictRestrictAlgEquivMapHom F L K L).range.comap (restrictNormalHom L) =
      (restrictRestrictAlgEquivMapHom F M K M).range := by
    ext σ
    simp only [Subgroup.mem_comap, MonoidHom.mem_range]
    have := Normal.tower_top_of_normal F K L
    refine ⟨fun ⟨τ, hτ⟩ ↦ ?_, fun ⟨τ, hτ⟩ ↦ ?_⟩
    · let τ' : Gal(M/K) := {
        toRingEquiv := σ
        commutes' r := by
          have := congr(algebraMap L M ($(hτ.symm) (algebraMap K L r)))
          simpa [restrictRestrictAlgEquivMapHom, ← IsScalarTower.algebraMap_apply K L M] using this
      }
      use τ'
      ext x
      simp [restrictRestrictAlgEquivMapHom, τ']
    · use τ.restrictNormal L
      rw [← hτ]
      ext x
      apply_fun _ using (algebraMap L M).injective
      simp [restrictRestrictAlgEquivMapHom]
  have h2 : (restrictNormalHom L).ker ≤ (restrictRestrictAlgEquivMapHom F M K M).range := by
    rw [← h1, ← MonoidHom.comap_bot]
    apply Subgroup.comap_mono
    simp
  convert Subgroup.relIndex_map_map_of_ker_inf_le (f := restrictNormalHom L)
    ((restrictRestrictAlgEquivMapHom F M K M).range ⊓ inertiaSubgroup F w) (inertiaSubgroup F w)
    inf_le_right (by gcongr)
  rw [← h1]
  apply SetLike.coe_injective
  exact (Set.image_preimage_inter ..).symm

open IntermediateField in
theorem ramificationIdxOfIsScalarTower_mul_ramificationIdxOfIsScalarTower
    (F K M : Type*) [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [Algebra M L]
    [IsScalarTower F M L] [IsScalarTower K M L] [IsScalarTower F K L] [Normal F L] [Normal K L]
    (v : AbsoluteValue L ℝ) :
    v.ramificationIdxOfIsScalarTower F K * v.ramificationIdxOfIsScalarTower K M =
      v.ramificationIdxOfIsScalarTower F M := by
  simp only [ramificationIdxOfIsScalarTower]
  rw [mul_comm, ← Subgroup.relIndex_map_map_of_injective _ _
      (restrictRestrictAlgEquivMapHom_injective_of_tower_top F K L), Subgroup.map_map,
    restrictRestrictAlgEquivMapHom_comp_restrictRestrictAlgEquivMapHom]
  apply Subgroup.relIndex_mul_relIndex
  · rw [← restrictRestrictAlgEquivMapHom_comp_restrictRestrictAlgEquivMapHom F L K L M L,
      ← Subgroup.map_map]
    exact Subgroup.map_mono (v.map_inertiaSubgroup_le K M)
  · exact v.map_inertiaSubgroup_le F K

/-- If `K / F` is an algebraic extension, `v` is a place of `K`, then the
ramification index of `v` for `K / F` is defined to be the ramification index of `w`
for `K / F`, where `w` is any extension of `v` to the algebraic closure of `K`. -/
noncomputable def ramificationIdx
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) : ℕ :=
  (v.exists_liesOver (AlgebraicClosure K)).choose.ramificationIdxOfIsScalarTower F K

/-- The ramification index is well-defined. -/
theorem ramificationIdx_spec
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    haveI := Algebra.IsAlgebraic.tower_bot F K L
    v.ramificationIdx F = w.ramificationIdxOfIsScalarTower F K := by
  have := Algebra.IsAlgebraic.tower_bot F K L
  rw [ramificationIdx]
  set v' := (v.exists_liesOver (AlgebraicClosure K)).choose
  have : v'.LiesOver v := (v.exists_liesOver (AlgebraicClosure K)).choose_spec
  have := Algebra.IsAlgebraic.tower_top (K := F) K (A := L)
  let i : L →ₐ[K] (AlgebraicClosure K) := IsAlgClosed.lift
  let := i.toAlgebra
  have := IsScalarTower.of_algHom i
  have := Algebra.IsAlgebraic.tower_top (K := K) L (A := AlgebraicClosure K)
  obtain ⟨w', _⟩ := w.exists_liesOver (AlgebraicClosure K)
  have : v'.comp (algebraMap K _).injective = w'.comp (algebraMap K _).injective := by
    have := LiesOver.trans w' w v
    rw [LiesOver.comp_eq v' v, LiesOver.comp_eq w' v]
  rw [ramificationIdxOfIsScalarTower_eq_of_comp_eq _ _ this]
  have := IsScalarTower.of_algHom (i.restrictScalars F)
  exact (ramificationIdxOfIsScalarTower_eq_of_liesOver ..).symm

/-- A place of `K` and its restriction to `K'` by an isomorphism `K' ≃ₐ[F] A` have the same
ramification index over `F`. -/
theorem ramificationIdx_comp_algEquiv_eq
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    {K' : Type*} [Field K'] [Algebra F K'] [Algebra.IsAlgebraic F K']
    (v : AbsoluteValue K ℝ) (f : K' ≃ₐ[F] K) :
    (v.comp (f := (f : K' →+* K)) f.injective).ramificationIdx F = v.ramificationIdx F := by
  set v' := v.comp (f := (f : K' →+* K)) f.injective
  let i := (IsScalarTower.toAlgHom F K (AlgebraicClosure K)).comp (f : K' →ₐ[F] K)
  let := i.toAlgebra
  have := IsScalarTower.of_algHom i
  obtain ⟨w, _⟩ := v.exists_liesOver (AlgebraicClosure K)
  have : w.LiesOver v' := by
    rw [liesOver_iff]
    ext x
    simp only [comp_apply, ← LiesOver.comp_eq w v, RingHom.coe_coe, v']
    rfl
  rw [ramificationIdx_spec F v w, ramificationIdx_spec F v' w]
  simpa using ramificationIdxOfIsScalarTower_comp_ringEquiv_eq w (RingEquiv.refl F) (f : K' ≃+* K)
    (RingEquiv.refl (AlgebraicClosure K)) (by ext; simp) (by ext; rfl)

/-- A generalization of `AbsoluteValue.ramificationIdx_comp_algEquiv_eq`. -/
theorem ramificationIdx_comp_ringEquiv_eq
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    {F' K' : Type*} [Field F'] [Field K'] [Algebra F' K'] [Algebra.IsAlgebraic F' K']
    (v : AbsoluteValue K ℝ) {f : F' →+* F} {g : K' ≃+* K}
    (hsurj : Function.Surjective f)
    (hcomp : (algebraMap F K).comp f = RingHom.comp g (algebraMap F' K')) :
    (v.comp (f := (g : K' →+* K)) g.injective).ramificationIdx F' = v.ramificationIdx F := by
  set v' := v.comp (f := (g : K' →+* K)) g.injective
  let f' := RingEquiv.ofBijective f ⟨f.injective, hsurj⟩
  let := ((algebraMap F (AlgebraicClosure K)).comp f).toAlgebra
  let := ((algebraMap K (AlgebraicClosure K)).comp (g : K' →+* K)).toAlgebra
  have : IsScalarTower F' K' (AlgebraicClosure K) := .of_algebraMap_eq fun x ↦
    congr(algebraMap K (AlgebraicClosure K) ($(hcomp) x))
  have : Normal F' (AlgebraicClosure K) := .of_equiv_equiv
      (f := f'.symm) (g := RingEquiv.refl _) <| by
    ext x
    obtain ⟨y, rfl⟩ := f'.surjective x
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.symm_apply_apply,
      RingEquiv.coe_ringHom_refl, RingHomCompTriple.comp_eq]
    rfl
  obtain ⟨w, _⟩ := v.exists_liesOver (AlgebraicClosure K)
  have : w.LiesOver v' := by
    rw [liesOver_iff]
    ext x
    simp only [comp_apply, ← LiesOver.comp_eq w v, RingHom.coe_coe, v']
    rfl
  rw [ramificationIdx_spec F v w, ramificationIdx_spec F' v' w]
  simpa using ramificationIdxOfIsScalarTower_comp_ringEquiv_eq w f' g
    (RingEquiv.refl (AlgebraicClosure K)) hcomp (by ext; rfl)

/-- If `K / F` is normal, then any two places of `K` which are the same when restricted to `F`
have the same ramification index over `F` (since they are conjugate). -/
theorem ramificationIdx_eq_of_comp_eq
    (F K : Type*) [Field F] [Field K] [Algebra F K] [Normal F K]
    {v w : AbsoluteValue K ℝ}
    (h : v.comp (algebraMap F K).injective = w.comp (algebraMap F K).injective) :
    v.ramificationIdx F = w.ramificationIdx F := by
  obtain ⟨σ, h⟩ := exists_algEquiv_comp_eq_of_comp_eq h.symm
  simpa only [h] using ramificationIdx_comp_algEquiv_eq F w σ

theorem ramificationIdx_mul_ramificationIdx
    (F K : Type*) {M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] [Algebra.IsAlgebraic F M]
    (v : AbsoluteValue M ℝ) (w : AbsoluteValue K ℝ) [v.LiesOver w] :
    haveI := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
    haveI := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
    w.ramificationIdx F * v.ramificationIdx K = v.ramificationIdx F := by
  have := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M)
  have := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M)
  obtain ⟨v', _⟩ := v.exists_liesOver (AlgebraicClosure M)
  have := LiesOver.trans v' v w
  rw [ramificationIdx_spec F w v', ramificationIdx_spec K v v', ramificationIdx_spec F v v',
    ramificationIdxOfIsScalarTower_mul_ramificationIdxOfIsScalarTower]

/-! ### Assertion that a place is unramified for an extension -/

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then `v` is
called unramified for `K / F`, if `Iᵥ(L/F) ≤ Gal(L/K)`, or equivalently `Iᵥ(L/K) = Iᵥ(L/F)`
(`AbsoluteValue.isUnramifiedOfIsScalarTower_iff_map_inertiaSubgroup_eq`).
Later we will show that this depends only on the place of `K` below `v`, and is independent of the
choice of `L` (`AbsoluteValue.isUnramified_spec`). -/
def IsUnramifiedOfIsScalarTower
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) : Prop :=
    v.inertiaSubgroup F ≤ (IntermediateField.restrictRestrictAlgEquivMapHom F L K L).range

theorem isUnramifiedOfIsScalarTower_iff_map_inertiaSubgroup_eq
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.IsUnramifiedOfIsScalarTower F K ↔ (v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) = v.inertiaSubgroup F := by
  have h := congr($(v.inertiaSubgroup_eq_comap F K).map
    (IntermediateField.restrictRestrictAlgEquivMapHom F L K L))
  rw [Subgroup.map_comap_eq] at h
  rw [h, inf_eq_right, IsUnramifiedOfIsScalarTower]

theorem isUnramifiedOfIsScalarTower_iff_ramificationIdxOfIsScalarTower_eq_one
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.IsUnramifiedOfIsScalarTower F K ↔ v.ramificationIdxOfIsScalarTower F K = 1 := by
  rw [isUnramifiedOfIsScalarTower_iff_map_inertiaSubgroup_eq, le_antisymm_iff]
  simp [ramificationIdxOfIsScalarTower, v.map_inertiaSubgroup_le F K]

/-- If `K / F` is an algebraic extension, `v` is a place of `K`, then `v` is called
unramified for `K / F`, if `w` is unramified for `K / F`, where `w` is any extension of `v` to the
algebraic closure of `K`. -/
def IsUnramified
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) : Prop :=
  (v.exists_liesOver (AlgebraicClosure K)).choose.IsUnramifiedOfIsScalarTower F K

theorem isUnramified_iff_ramificationIdx_eq_one
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) :
    v.IsUnramified F ↔ v.ramificationIdx F = 1 :=
  isUnramifiedOfIsScalarTower_iff_ramificationIdxOfIsScalarTower_eq_one ..

theorem isUnramified_spec
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    haveI := Algebra.IsAlgebraic.tower_bot F K L
    v.IsUnramified F ↔ w.IsUnramifiedOfIsScalarTower F K := by
  rw [isUnramified_iff_ramificationIdx_eq_one, v.ramificationIdx_spec F w,
    isUnramifiedOfIsScalarTower_iff_ramificationIdxOfIsScalarTower_eq_one]

theorem isUnramified_comp_algEquiv_iff
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    {K' : Type*} [Field K'] [Algebra F K'] [Algebra.IsAlgebraic F K']
    (v : AbsoluteValue K ℝ) (f : K' ≃ₐ[F] K) :
    (v.comp (f := (f : K' →+* K)) f.injective).IsUnramified F ↔ v.IsUnramified F := by
  simp only [isUnramified_iff_ramificationIdx_eq_one, ramificationIdx_comp_algEquiv_eq]

theorem isUnramified_comp_ringEquiv_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    {F' K' : Type*} [Field F'] [Field K'] [Algebra F' K'] [Algebra.IsAlgebraic F' K']
    (v : AbsoluteValue K ℝ) {f : F' →+* F} {g : K' ≃+* K}
    (hsurj : Function.Surjective f)
    (hcomp : (algebraMap F K).comp f = RingHom.comp g (algebraMap F' K')) :
    (v.comp (f := (g : K' →+* K)) g.injective).IsUnramified F' ↔ v.IsUnramified F := by
  simp only [isUnramified_iff_ramificationIdx_eq_one,
    ramificationIdx_comp_ringEquiv_eq v hsurj hcomp]

theorem isUnramified_iff_of_comp_eq
    (F K : Type*) [Field F] [Field K] [Algebra F K] [Normal F K]
    {v w : AbsoluteValue K ℝ}
    (h : v.comp (algebraMap F K).injective = w.comp (algebraMap F K).injective) :
    v.IsUnramified F ↔ w.IsUnramified F := by
  simp only [isUnramified_iff_ramificationIdx_eq_one, ramificationIdx_eq_of_comp_eq F K h]

namespace IsUnramified

theorem tower_top
    {F : Type*} (K : Type*) {M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] [Algebra.IsAlgebraic F M]
    {v : AbsoluteValue M ℝ} (H : v.IsUnramified F) :
    haveI := Algebra.IsAlgebraic.tower_top (K := F) (L := K) (A := M); v.IsUnramified K := by
  simp only [isUnramified_iff_ramificationIdx_eq_one] at H ⊢
  rw [← v.ramificationIdx_mul_ramificationIdx F K (v.comp (algebraMap K M).injective),
    mul_eq_one] at H
  exact H.2

theorem tower_bot
    {F K M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] [Algebra.IsAlgebraic F M]
    {v : AbsoluteValue M ℝ} (H : v.IsUnramified F) (w : AbsoluteValue K ℝ) [v.LiesOver w] :
    haveI := Algebra.IsAlgebraic.tower_bot (K := F) (L := K) (A := M); w.IsUnramified F := by
  simp only [isUnramified_iff_ramificationIdx_eq_one] at H ⊢
  rw [← v.ramificationIdx_mul_ramificationIdx F K w, mul_eq_one] at H
  exact H.1

theorem trans
    {F K M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [Algebra.IsAlgebraic F K] [Algebra.IsAlgebraic K M]
    {v : AbsoluteValue M ℝ} {w : AbsoluteValue K ℝ} (H1 : w.IsUnramified F)
    (H2 : v.IsUnramified K) [v.LiesOver w] :
    haveI := Algebra.IsAlgebraic.trans F K M; v.IsUnramified F := by
  have := Algebra.IsAlgebraic.trans F K M
  simp only [isUnramified_iff_ramificationIdx_eq_one] at H1 H2 ⊢
  rw [← v.ramificationIdx_mul_ramificationIdx F K w, H1, H2, one_mul]

end IsUnramified

/-- If `L / K` is an algebraic extension, `L / F` is a field extension, `v` is a place of `F`, then
`v` is called unramified for `L / K`, if all place `w` of `L` above `v` is
unramified for `L / K`. -/
def IsUnramifiedIn
    {F : Type*} (K L : Type*) [Field F] [Field K] [Field L]
    [Algebra F L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue F ℝ) : Prop :=
    ∀ w : AbsoluteValue L ℝ, w.LiesOver v → w.IsUnramified K

@[simp]
theorem isUnramifiedIn_self_iff
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) :
    v.IsUnramifiedIn F K ↔ v.IsUnramified F := by
  simp [IsUnramifiedIn, liesOver_self_iff]

namespace IsUnramifiedIn

theorem tower_top
    {F K : Type*} (L : Type*) {M : Type*} [Field F] [Field K] [Field L] [Field M]
    [Algebra F L] [Algebra F M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsAlgebraic K M]
    {v : AbsoluteValue F ℝ} (H : v.IsUnramifiedIn K M) :
    haveI := Algebra.IsAlgebraic.tower_top (K := K) (L := L) (A := M); v.IsUnramifiedIn L M := by
  simp only [IsUnramifiedIn] at H ⊢
  peel H with w _ h
  exact h.tower_top L

theorem tower_bot
    {F K : Type*} (L : Type*) {M : Type*} [Field F] [Field K] [Field L] [Field M]
    [Algebra F L] [Algebra F M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsScalarTower F L M] [Algebra.IsAlgebraic K M]
    {v : AbsoluteValue F ℝ} (H : v.IsUnramifiedIn K M) :
    haveI := Algebra.IsAlgebraic.tower_bot (K := K) (L := L) (A := M); v.IsUnramifiedIn K L := by
  simp only [IsUnramifiedIn] at H ⊢
  intro u _
  have := Algebra.IsAlgebraic.tower_top (K := K) (L := L) (A := M)
  obtain ⟨w, _⟩ := u.exists_liesOver M
  exact (H w (.trans w u v)).tower_bot u

theorem trans
    {F K L M : Type*} [Field F] [Field K] [Field L] [Field M]
    [Algebra F L] [Algebra F M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsScalarTower F L M] [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic L M]
    {v : AbsoluteValue F ℝ} (H1 : v.IsUnramifiedIn K L) (H2 : v.IsUnramifiedIn L M) :
    haveI := Algebra.IsAlgebraic.trans K L M; v.IsUnramifiedIn K M := by
  simp only [IsUnramifiedIn] at H1 H2 ⊢
  peel H2 with w _ h
  exact (H1 _ (.tower_bot w (w.comp (algebraMap L M).injective) v)).trans h

end IsUnramifiedIn

theorem isUnramifiedIn_comp_ringEquiv_iff
    {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F L] [Algebra K L]
    [Algebra.IsAlgebraic K L] {F' K' L' : Type*} [Field F'] [Field K'] [Field L'] [Algebra F' L']
    [Algebra K' L'] [Algebra.IsAlgebraic K' L']
    (v : AbsoluteValue F ℝ) {e : F' ≃+* F} {f : K' ≃+* K} {g : L' ≃+* L}
    (hcomp0 : (algebraMap F L).comp e = RingHom.comp g (algebraMap F' L'))
    (hcomp : (algebraMap K L).comp f = RingHom.comp g (algebraMap K' L')) :
    (v.comp (f := (e : F' →+* F)) e.injective).IsUnramifiedIn K' L' ↔ v.IsUnramifiedIn K L := by
  simp only [IsUnramifiedIn, liesOver_iff]
  refine ⟨fun H w h ↦ ?_, fun H w h ↦ ?_⟩
  · specialize H (w.comp (f := (g : L' →+* L)) g.injective) <| by
      ext x
      trans w (algebraMap F L (e x))
      · simpa using congr(w ($(hcomp0.symm) x))
      · simpa using congr($h (e x))
    rwa [w.isUnramified_comp_ringEquiv_iff f.surjective hcomp] at H
  · specialize H (w.comp (f := (g.symm : L →+* L')) g.symm.injective) <| by
      ext x
      trans w (algebraMap F' L' (e.symm x))
      · simpa using congr(w (g.symm ($(hcomp0) (e.symm x))))
      · simpa using congr($h (e.symm x))
    have := w.isUnramified_comp_ringEquiv_iff (f := (f.symm : K →+* K')) (g := g.symm)
        f.symm.surjective <| by
      ext x
      simpa using congr(g.symm ($(hcomp.symm) (f.symm x)))
    rwa [this] at H

theorem isUnramifiedIn_iff_of_algEquiv
    {F K L L' : Type*} [Field F] [Field K] [Field L] [Field L'] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra F L'] [Algebra K L'] [IsScalarTower F K L] [IsScalarTower F K L']
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K L']
    (v : AbsoluteValue F ℝ) (f : L ≃ₐ[K] L') :
    v.IsUnramifiedIn K L ↔ v.IsUnramifiedIn K L' := by
  simpa using v.isUnramifiedIn_comp_ringEquiv_iff (e := RingEquiv.refl F) (f := RingEquiv.refl K)
    (g := (f : L ≃+* L'))
    (by ext; simp [IsScalarTower.algebraMap_apply F K L, IsScalarTower.algebraMap_apply F K L'])
    (by ext; simp)

end AbsoluteValue
