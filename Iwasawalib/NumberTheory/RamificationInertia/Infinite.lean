/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

@[expose] public section

/-!

# Inertia subgroup, etc. for an infinite extension of algebraic number fields

We will use the following conventions:

- A place of an arbitrary field is a non-trivial `AbsoluteValue` of it to `ℝ`.
- A place is called finite, if it is non-archimedean.
- A place is called archimedean or infinite, if it is not non-archimedean.

References:

- J. W. S. Cassels. *Global Fields*. Chapter II in J. W. S. Cassels,
  A. Frohlich, editors, *Algebraic Number Theory*.

-/

namespace AbsoluteValue

/-- **Gelfand-Tornheim theorem**: if a field `K` has an infinite place,
then there exists an embedding `K →+* ℂ` such that the absolute value is *equivalent* to
the usual absolute value on `ℂ`.

Proof: see E. Artin, *Theory of Algebraic Numbers*, pp. 45 and 67. -/
theorem exists_ringHom_complex_of_not_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (h1 : v.IsNontrivial) (h2 : ¬IsNonarchimedean v) :
    ∃ φ : K →+* ℂ, NumberField.place φ ≈ v := by
  sorry

/-- A non-archimedean absolute value is a valuation. -/
@[simps]
def toValuation
    {R : Type*} [Ring R] [Nontrivial R] (v : AbsoluteValue R ℝ) (h : IsNonarchimedean v) :
    Valuation R NNReal where
  toFun x := ⟨v x, v.nonneg' x⟩
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by ext1; simp
  map_add_le_max' x y := h x y

/-! ### Decomposition subgroup for a place -/

/-- The decomposition subgroup `Dᵥ(K/F)` in `Gal(K/F)` for a place `v` of `K` consists of all `σ`
preserving the set `{x | v x ≤ 1}`. This definition also works for infinite places. -/
def decompositionSubgroup
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) :
    Subgroup Gal(K/F) where
  carrier := {σ | σ '' {x | v x ≤ 1} = {x | v x ≤ 1}}
  one_mem' := by simp
  mul_mem' {f} {g} hf hg := by
    change (f ∘ g) '' _ = _
    rw [Set.image_comp]
    simp_all
  inv_mem' {f} hf := by
    simp only [Set.mem_setOf_eq] at hf ⊢
    apply_fun ((f⁻¹ :) '' ·) at hf
    rw [← Set.image_comp, eq_comm] at hf
    change _ = (f⁻¹ * f) '' _ at hf
    simpa only [inv_mul_cancel, AlgEquiv.one_apply, Set.image_id'] using hf

theorem mem_decompositionSubgroup_iff
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) (σ) :
    σ ∈ v.decompositionSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} := Iff.rfl

theorem apply_le_one_of_mem_decompositionSubgroup
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.decompositionSubgroup F) {x} (hx : v x ≤ 1) : v (σ x) ≤ 1 :=
  h.le ⟨x, hx, rfl⟩

theorem apply_le_one_iff_of_mem_decompositionSubgroup
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.decompositionSubgroup F) {x} : v (σ x) ≤ 1 ↔ v x ≤ 1 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ v.apply_le_one_of_mem_decompositionSubgroup h hx⟩
  simpa using v.apply_le_one_of_mem_decompositionSubgroup (inv_mem h) hx

/-- Our definition is the same as `ValuationSubring.decompositionSubgroup` for finite places. -/
theorem decompositionSubgroup_eq_of_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : IsNonarchimedean v) :
    v.decompositionSubgroup F = (v.toValuation h).valuationSubring.decompositionSubgroup F := by
  ext g
  simp only [mem_decompositionSubgroup_iff, MulAction.mem_stabilizer_iff, SetLike.ext'_iff]
  congr!

/-! ### Inertia subgroup for a place -/

/-- The inertia subgroup `Iᵥ(K/F)` in `Gal(K/F)` for a finite place `v` of `K` consists of all `σ`
preserving the set `{x | v x ≤ 1}` and such that for all such `x`, `v (σ x - x) < 1`.
For infinite places `Iᵥ(K/F)` is just defined to be the decomposition subgroup `Dᵥ(K/F)`. -/
def inertiaSubgroup
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) :
    Subgroup Gal(K/F) where
  carrier := {σ | σ '' {x | v x ≤ 1} = {x | v x ≤ 1} ∧
    (¬IsNonarchimedean v ∨ ∀ x, v x ≤ 1 → v (σ x - x) < 1)}
  one_mem' := by simp
  mul_mem' {f} {g} hf hg := by
    by_cases h : IsNonarchimedean v
    · simp only [h, not_true_eq_false, false_or] at hf hg ⊢
      use (v.decompositionSubgroup F).mul_mem hf.1 hg.1
      intro x hx
      rw [AlgEquiv.mul_apply]
      replace hf := hf.2 _ (v.apply_le_one_of_mem_decompositionSubgroup hg.1 hx)
      replace hg := hg.2 _ hx
      simpa using (h (f (g x) - g x) (g x - x)).trans_lt (max_lt hf hg)
    simp only [h, not_false_eq_true, true_or, and_true] at hf hg ⊢
    exact (v.decompositionSubgroup F).mul_mem hf hg
  inv_mem' {f} hf := by
    by_cases h : IsNonarchimedean v
    · simp only [h, not_true_eq_false, false_or] at hf ⊢
      have h1 := (v.decompositionSubgroup F).inv_mem hf.1
      refine ⟨h1, fun x hx ↦ ?_⟩
      rw [← AbsoluteValue.map_neg]
      convert hf.2 _ (v.apply_le_one_of_mem_decompositionSubgroup h1 hx) using 2
      simp
    simp only [h, not_false_eq_true, true_or, and_true] at hf ⊢
    exact (v.decompositionSubgroup F).inv_mem hf

theorem mem_inertiaSubgroup_iff
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) (σ) :
    σ ∈ v.inertiaSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} ∧
      (¬IsNonarchimedean v ∨ ∀ x, v x ≤ 1 → v (σ x - x) < 1) := Iff.rfl

theorem mem_inertiaSubgroup_iff_of_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : IsNonarchimedean v) (σ) :
    σ ∈ v.inertiaSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} ∧
      ∀ x, v x ≤ 1 → v (σ x - x) < 1 := by
  simp [mem_inertiaSubgroup_iff, h]

theorem mem_inertiaSubgroup_iff_of_not_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬IsNonarchimedean v) (σ) :
    σ ∈ v.inertiaSubgroup F ↔ σ '' {x | v x ≤ 1} = {x | v x ≤ 1} := by
  simp [mem_inertiaSubgroup_iff, h]

theorem inertiaSubgroup_le_decompositionSubgroup
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) :
    v.inertiaSubgroup F ≤ v.decompositionSubgroup F := fun _ ↦ by
  simpa only [mem_inertiaSubgroup_iff, mem_decompositionSubgroup_iff] using And.left

theorem inertiaSubgroup_eq_decompositionSubgroup_of_not_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬IsNonarchimedean v) :
    v.inertiaSubgroup F = v.decompositionSubgroup F := by
  ext
  simp only [v.mem_inertiaSubgroup_iff_of_not_isNonarchimedean F h, mem_decompositionSubgroup_iff]

theorem apply_le_one_of_mem_inertiaSubgroup
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.inertiaSubgroup F) {x} (hx : v x ≤ 1) : v (σ x) ≤ 1 :=
  v.apply_le_one_of_mem_decompositionSubgroup (v.inertiaSubgroup_le_decompositionSubgroup F h) hx

theorem apply_le_one_iff_of_mem_inertiaSubgroup
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.inertiaSubgroup F) {x} : v (σ x) ≤ 1 ↔ v x ≤ 1 :=
  v.apply_le_one_iff_of_mem_decompositionSubgroup (v.inertiaSubgroup_le_decompositionSubgroup F h)

theorem apply_sub_lt_one_of_mem_inertiaSubgroup_of_isNonarchimedean
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.inertiaSubgroup F) (h2 : IsNonarchimedean v) {x} (hx : v x ≤ 1) : v (σ x - x) < 1 :=
  ((v.mem_inertiaSubgroup_iff_of_isNonarchimedean F h2 σ).1 h).2 x hx

/-- Our definition is the same as `ValuationSubring.inertiaSubgroup` for finite places. -/
theorem inertiaSubgroup_eq_of_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : IsNonarchimedean v) :
    v.inertiaSubgroup F =
      ((v.toValuation h).valuationSubring.inertiaSubgroup F).map (Subgroup.subtype _) := by
  ext g
  rw [Subgroup.mem_map]
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have := v.inertiaSubgroup_le_decompositionSubgroup _ hg
    rw [v.decompositionSubgroup_eq_of_isNonarchimedean _ h] at this
    refine ⟨⟨g, this⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    change IsLocalRing.residue _ _ = IsLocalRing.residue _ _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff,
      ← NNReal.coe_lt_coe, NNReal.coe_one]
    convert v.apply_sub_lt_one_of_mem_inertiaSubgroup_of_isNonarchimedean hg h y.2
  · rintro ⟨f, h1, h2⟩
    rw [v.mem_inertiaSubgroup_iff_of_isNonarchimedean F h]
    refine ⟨?_, fun x hx ↦ ?_⟩
    · rw [← v.mem_decompositionSubgroup_iff F, ← h2]
      have := v.decompositionSubgroup_eq_of_isNonarchimedean F h
      convert f.2
    · rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at h1
      replace h1 := congr($(h1) (IsLocalRing.residue _ ⟨x, hx⟩))
      change IsLocalRing.residue _ _ = IsLocalRing.residue _ _ at h1
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff,
        ← NNReal.coe_lt_coe, NNReal.coe_one] at h1
      rw [← h2]
      exact h1

/-! ### Assertion that a place is unramified -/

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Dᵥ(L/K) = Dᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem decompositionSubgroup_eq_comap
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.decompositionSubgroup K = (v.decompositionSubgroup F).comap
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  sorry

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) ≤ Iᵥ(L/F)`. -/
theorem map_decompositionSubgroup_le
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    (v.decompositionSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) ≤ v.decompositionSubgroup F := by
  simpa only [Subgroup.map_le_iff_le_comap] using (v.decompositionSubgroup_eq_comap F K).le

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) = Iᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem inertiaSubgroup_eq_comap
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.inertiaSubgroup K = (v.inertiaSubgroup F).comap
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  sorry

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) ≤ Iᵥ(L/F)`. -/
theorem map_inertiaSubgroup_le
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    (v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) ≤ v.inertiaSubgroup F := by
  simpa only [Subgroup.map_le_iff_le_comap] using (v.inertiaSubgroup_eq_comap F K).le

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then `v` is
called unramified in `L / K`, if `Iᵥ(L/F) ≤ Gal(L/K)`, or equivalently `Iᵥ(L/K) = Iᵥ(L/F)`. -/
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

end AbsoluteValue
