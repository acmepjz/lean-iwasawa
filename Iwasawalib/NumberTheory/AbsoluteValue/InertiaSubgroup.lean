/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Iwasawalib.NumberTheory.AbsoluteValue.DecompositionSubgroup
public import Iwasawalib.NumberTheory.AbsoluteValue.GelfandTornheim
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Iwasawalib.Topology.Algebra.Group.Basic

@[expose] public section

/-!

# Inertia subgroup for a place (`AbsoluteValue`)

(To be written)

References:

- [J. W. S. Cassels, A. Frohlich, editors, *Algebraic Number Theory*][cassels1967algebraic]

-/

namespace AbsoluteValue

/-! ### Inertia subgroup for a place -/

section General

variable (F K S : Type*) [CommSemiring F] [Ring K] [Algebra F K] [Semiring S] [Nontrivial S]
  [LinearOrder S] [ZeroLEOneClass S] [MulPosMono S] (v : AbsoluteValue K S) (σ : K ≃ₐ[F] K)

variable {K S}

/-- Another version of `AbsoluteValue.map_neg` with slightly different assumptions.

TODO: go mathlib -/
theorem map_neg' {R S : Type*} [Semiring S] [LinearOrder S] [MulPosMono S] [Ring R]
    (abv : AbsoluteValue R S) (a : R) : abv (-a) = abv a := by
  by_contra! H
  wlog H' : abv (-a) < abv a generalizing a
  · specialize this (-a)
    simp only [neg_neg] at this
    exact this H.symm (H.lt_or_gt.resolve_left H')
  have h1 : abv (-1) < 1 := by
    by_contra! h1
    have := le_mul_of_one_le_left (abv.nonneg a) h1
    rw [← map_mul, neg_one_mul] at this
    exact this.not_gt H'
  have := mul_le_of_le_one_left (abv.nonneg (-a)) h1.le
  rw [← map_mul, neg_one_mul, neg_neg] at this
  exact this.not_gt H'

/-- The inertia subgroup `Iᵥ(K/F)` in `Gal(K/F)` for a finite place `v` of `K` consists of all `σ`
in the decomposition subgroup `Dᵥ(K/F)` such that for all `x` with `v x ≤ 1`, `v (σ x - x) < 1`.
For infinite places `Iᵥ(K/F)` is just defined to be the decomposition subgroup `Dᵥ(K/F)`. -/
def inertiaSubgroup : Subgroup (K ≃ₐ[F] K) where
  carrier := {σ | σ ∈ v.decompositionSubgroup F ∧
    (¬IsNonarchimedean v ∨ ∀ x, v x ≤ 1 → v (σ x - x) < 1)}
  one_mem' := by simp
  mul_mem' {f} {g} hf hg := by
    by_cases h : IsNonarchimedean v
    · simp only [h, not_true_eq_false, false_or, Set.mem_setOf] at hf hg ⊢
      obtain ⟨hf1, hf2⟩ := hf
      obtain ⟨hg1, hg2⟩ := hg
      use mul_mem hf1 hg1
      intro x hx
      simpa using (h (f (g x) - g x) (g x - x)).trans_lt <| max_lt
        (hf2 (g x) (by rwa [v.apply_eq_of_mem_decompositionSubgroup hg1])) (hg2 _ hx)
    simp only [h, not_false_eq_true, true_or, and_true, Set.mem_setOf] at hf hg ⊢
    exact mul_mem hf hg
  inv_mem' {f} hf := by
    by_cases h : IsNonarchimedean v
    · simp only [h, not_true_eq_false, false_or, Set.mem_setOf] at hf ⊢
      have h1 := inv_mem hf.1
      refine ⟨h1, fun x hx ↦ ?_⟩
      rw [← v.map_neg']
      convert hf.2 _ (v.apply_eq_of_mem_decompositionSubgroup h1 x ▸ hx) using 2
      simp
    simpa [h] using hf

variable {F}

theorem mem_inertiaSubgroup_iff :
    σ ∈ v.inertiaSubgroup F ↔ σ ∈ v.decompositionSubgroup F ∧
      (¬IsNonarchimedean v ∨ ∀ x, v x ≤ 1 → v (σ x - x) < 1) := Iff.rfl

theorem mem_inertiaSubgroup_iff_of_isNonarchimedean (h : IsNonarchimedean v) (σ) :
    σ ∈ v.inertiaSubgroup F ↔ σ ∈ v.decompositionSubgroup F ∧
      ∀ x, v x ≤ 1 → v (σ x - x) < 1 := by
  simp [mem_inertiaSubgroup_iff, h]

theorem mem_inertiaSubgroup_iff_of_not_isNonarchimedean (h : ¬IsNonarchimedean v) (σ) :
    σ ∈ v.inertiaSubgroup F ↔ σ ∈ v.decompositionSubgroup F := by
  simp [mem_inertiaSubgroup_iff, h]

theorem inertiaSubgroup_eq_bot_of_not_isNontrivial
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬v.IsNontrivial) : v.inertiaSubgroup F = ⊥ := by
  rw [eq_bot_iff]
  rintro σ hσ
  rw [Subgroup.mem_bot]
  ext x
  rw [v.mem_inertiaSubgroup_iff_of_isNonarchimedean (by
    contrapose! h; exact isNontrivial_of_not_isNonarchimedean _ h)] at hσ
  replace hσ := hσ.2 x <| by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (not_isNontrivial_apply h hx).le
  replace hσ : σ x - x = 0 := by
    contrapose! hσ
    exact (not_isNontrivial_apply h hσ).ge
  simpa [sub_eq_zero] using hσ

variable (F)

theorem inertiaSubgroup_le_decompositionSubgroup :
    v.inertiaSubgroup F ≤ v.decompositionSubgroup F := fun _ ↦ by
  simpa only [mem_inertiaSubgroup_iff] using And.left

theorem inertiaSubgroup_eq_decompositionSubgroup_of_not_isNonarchimedean (h : ¬IsNonarchimedean v) :
    v.inertiaSubgroup F = v.decompositionSubgroup F := by
  ext
  simp only [v.mem_inertiaSubgroup_iff_of_not_isNonarchimedean h]

variable {F σ}

theorem apply_eq_of_mem_inertiaSubgroup
    (h : σ ∈ v.inertiaSubgroup F) (x) : v (σ x) = v x :=
  v.apply_eq_of_mem_decompositionSubgroup (v.inertiaSubgroup_le_decompositionSubgroup F h) x

theorem apply_sub_lt_one_of_mem_inertiaSubgroup_of_isNonarchimedean
    (h : σ ∈ v.inertiaSubgroup F) (h2 : IsNonarchimedean v) {x} (hx : v x ≤ 1) : v (σ x - x) < 1 :=
  ((v.mem_inertiaSubgroup_iff_of_isNonarchimedean h2 σ).1 h).2 x hx

/-- Our definition is the same as `ValuationSubring.inertiaSubgroup` for finite places. -/
theorem inertiaSubgroup_eq_of_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) (h : IsNonarchimedean v) :
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
    rw [v.mem_inertiaSubgroup_iff_of_isNonarchimedean h]
    refine ⟨?_, fun x hx ↦ ?_⟩
    · rw [v.decompositionSubgroup_eq_of_isNonarchimedean _ h, ← h2]
      convert f.2
    · rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at h1
      replace h1 := congr($(h1) (IsLocalRing.residue _ ⟨x, hx⟩))
      change IsLocalRing.residue _ _ = IsLocalRing.residue _ _ at h1
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff,
        ← NNReal.coe_lt_coe, NNReal.coe_one] at h1
      rwa [← h2]

theorem inertiaSubgroup_comp_algEquiv_eq_comap {K' : Type*} [Ring K'] [Algebra F K']
    (f : K' ≃ₐ[F] K) :
    (v.comp (f := (f : K' →+* K)) f.injective).inertiaSubgroup F =
      (v.inertiaSubgroup F).comap f.autCongr := by
  ext σ
  simp only [mem_inertiaSubgroup_iff, decompositionSubgroup_comp_algEquiv_eq_comap,
    Subgroup.mem_comap, and_congr_right_iff]
  refine fun _ ↦ or_congr ?_ ?_
  · simp only [IsNonarchimedean, comp_apply, RingHom.coe_coe, map_add, le_sup_iff, not_forall,
      not_or, not_le]
    refine ⟨fun ⟨x, y, H⟩ ↦ ⟨f x, f y, ?_⟩, fun ⟨x, y, H⟩ ↦ ⟨f.symm x, f.symm y, ?_⟩⟩ <;> simpa
  · simp only [comp_apply, RingHom.coe_coe, map_sub, MonoidHom.coe_coe, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply]
    refine ⟨fun H x hx ↦ ?_, fun H x hx ↦ ?_⟩
    · simpa using H (f.symm x) (by simpa)
    · simpa using H (f x) hx

theorem inertiaSubgroup_comp_ringEquiv_eq_comap
    {F E : Type*} [CommSemiring F] [Ring E] [Algebra F E]
    {M N : Type*} [CommSemiring M] [Ring N] [Algebra M N]
    {f : F →+* M} {g : E ≃+* N} (v : AbsoluteValue N S)
    (hsurj : Function.Surjective f)
    (hcomp : (algebraMap M N).comp f = RingHom.comp g (algebraMap F E)) :
    (v.comp (f := (g : E →+* N)) g.injective).inertiaSubgroup F =
      (v.inertiaSubgroup M).comap (AlgEquiv.autCongrOfSurjective hsurj hcomp) := by
  ext σ
  simp only [mem_inertiaSubgroup_iff, v.decompositionSubgroup_comp_ringEquiv_eq_comap hsurj hcomp,
    Subgroup.mem_comap, and_congr_right_iff]
  refine fun _ ↦ or_congr ?_ ?_
  · simp only [IsNonarchimedean, comp_apply, RingHom.coe_coe, map_add, le_sup_iff, not_forall,
      not_or, not_le]
    refine ⟨fun ⟨x, y, H⟩ ↦ ⟨g x, g y, ?_⟩, fun ⟨x, y, H⟩ ↦ ⟨g.symm x, g.symm y, ?_⟩⟩ <;> simpa
  · simp only [comp_apply, RingHom.coe_coe, map_sub, MonoidHom.coe_coe,
      AlgEquiv.autCongrOfSurjective_apply_apply]
    refine ⟨fun H x hx ↦ ?_, fun H x hx ↦ ?_⟩
    · simpa using H (g.symm x) (by simpa)
    · simpa using H (g x) hx

open scoped Pointwise in
theorem inertiaSubgroup_comp_algEquiv_eq_smul (f : K ≃ₐ[F] K) :
    (v.comp (f := (f : K →+* K)) f.injective).inertiaSubgroup F =
      (MulAut.conj f)⁻¹ • v.inertiaSubgroup F := by
  rw [inertiaSubgroup_comp_algEquiv_eq_comap]
  ext σ
  simp only [Subgroup.mem_comap, MonoidHom.coe_coe, AlgEquiv.autCongr_apply,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, MulAut.smul_def, MulAut.conj_apply]
  rfl

end General

section IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
  {S : Type*} [Semiring S] [Nontrivial S] [LinearOrder S] [ZeroLEOneClass S] [MulPosMono S]
  (v : AbsoluteValue L S)

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) = Iᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem inertiaSubgroup_eq_comap :
    v.inertiaSubgroup K = (v.inertiaSubgroup F).comap
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  ext
  simp only [mem_inertiaSubgroup_iff, Subgroup.mem_comap, v.decompositionSubgroup_eq_comap F K]
  congr!
  ext
  simp [IntermediateField.restrictRestrictAlgEquivMapHom]

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) ≤ Iᵥ(L/F)`. -/
theorem map_inertiaSubgroup_le :
    (v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) ≤ v.inertiaSubgroup F := by
  simpa only [Subgroup.map_le_iff_le_comap] using (v.inertiaSubgroup_eq_comap F K).le

end IsScalarTower

/-- If `L / K / F` is an extension tower, `L / F` and `K / F` are Galois, `v` and `w` are places of
`K` and `L`, respectively, such that `w` lies over `v`, then the image of `I_w(L/F)` in `Gal(K/F)`
is equal to `Iᵥ(K/F)`. -/
theorem map_inertiaSubgroup_eq_of_liesOver
    (F : Type*) {K L : Type*} [Field F] [Field K] [Algebra F K] [Field L]
    [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F K] [Normal F L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    (w.inertiaSubgroup F).map (AlgEquiv.restrictNormalHom K) =
      v.inertiaSubgroup F := by
  rw [← LiesOver.comp_eq w v]
  by_cases hw : IsNonarchimedean w
  · have hv := (w.isNonarchimedean_comp_iff (algebraMap K L)).2 hw
    ext σ
    simp only [Subgroup.mem_map, mem_inertiaSubgroup_iff_of_isNonarchimedean _ hw,
      mem_inertiaSubgroup_iff_of_isNonarchimedean _ hv]
    refine ⟨fun ⟨τ, ⟨hτ1, hτ2⟩, hτ3⟩ ↦ ⟨?_, fun x hx ↦ ?_⟩, fun ⟨hσ1, hσ2⟩ ↦ ?_⟩
    · simpa only [map_decompositionSubgroup_eq_of_liesOver F (w.comp (algebraMap K L).injective) w,
        hτ3] using Subgroup.mem_map_of_mem (AlgEquiv.restrictNormalHom K) hτ1
    · simpa [← hτ3, AlgEquiv.restrictNormalHom] using hτ2 (algebraMap K L x) (by simpa using hx)
    · have := hσ1
      rw [← map_decompositionSubgroup_eq_of_liesOver F (w.comp (algebraMap K L).injective) w,
        Subgroup.mem_map] at this
      obtain ⟨τ, hτ1, hτ2⟩ := this
      /-
      Suppose `σ ∈ Iᵥ(K/F)`, now we have found `τ ∈ D_w(L/F)` such that `τ|_K = σ`.
      Next steps: the image of `τ` in `Gal(k_w/kᵤ)` is contained in `Gal(k_w/kᵥ)` since its
      image in `Gal(kᵥ/kᵤ)` is trivial (here we denote `u` the restriction of `w` to `F`).
      We can find a preimage `τ₁ ∈ D_w(L/K)` of it, since the map `D_w(L/K) → Gal(k_w/kᵥ)`
      is surjective. Then `τ * (τ₁)⁻¹ ∈ I_w(L/F)` whose restriction to `K` is `σ`.
      A lot of API is still missing.
      -/
      sorry
  have hv := (w.isNonarchimedean_comp_iff (algebraMap K L)).not.2 hw
  rw [inertiaSubgroup_eq_decompositionSubgroup_of_not_isNonarchimedean _ _ hw,
    inertiaSubgroup_eq_decompositionSubgroup_of_not_isNonarchimedean _ _ hv]
  exact map_decompositionSubgroup_eq_of_liesOver ..

end AbsoluteValue
