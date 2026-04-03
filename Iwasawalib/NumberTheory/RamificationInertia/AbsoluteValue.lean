/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.Ostrowski

@[expose] public section

/-!

# Ramification index and inertia subgroup for a place (`AbsoluteValue`)

We will use the following conventions:

- A place of an arbitrary field is a non-trivial `AbsoluteValue` of it to `ℝ`.
- A place is called finite, if it is non-archimedean.
- A place is called archimedean or infinite, if it is not non-archimedean.

References:

- J. W. S. Cassels. *Global Fields*. Chapter II in J. W. S. Cassels,
  A. Frohlich, editors, *Algebraic Number Theory*.

-/

namespace AbsoluteValue

/-- TODO: go mathlib -/
@[simp]
theorem comp_apply {R S T : Type*} [Semiring T] [Semiring R] [Semiring S] [PartialOrder S]
    (v : AbsoluteValue R S) {f : T →+* R} (hf : Function.Injective f) (x) :
    v.comp hf x = v (f x) := rfl

/-- TODO: go mathlib -/
@[simp]
theorem comp_id {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (v : AbsoluteValue R S) :
    v.comp (f := RingHom.id R) Function.injective_id = v := rfl

/-- TODO: go mathlib -/
theorem IsEquiv.comp {R S T : Type*} [Semiring T] [Semiring R] [Semiring S] [PartialOrder S]
    {v w : AbsoluteValue R S} (h : v.IsEquiv w) {f : T →+* R} (hf : Function.Injective f) :
    (v.comp hf).IsEquiv (w.comp hf) := by
  simp_all [IsEquiv]

/-- TODO: use `@[mk_iff]` instead -/
theorem liesOver_iff {K L S : Type*} [CommRing K] [IsSimpleRing K] [CommRing L] [Algebra K L]
    [PartialOrder S] [Nontrivial L] [Semiring S] {w : AbsoluteValue L S} {v : AbsoluteValue K S} :
    w.LiesOver v ↔ w.comp (algebraMap K L).injective = v :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/-- TODO: go mathlib -/
instance liesOver_comp {K L S : Type*} [CommRing K] [IsSimpleRing K] [CommRing L] [Algebra K L]
    [PartialOrder S] [Nontrivial L] [Semiring S] (w : AbsoluteValue L S) :
    w.LiesOver (w.comp (algebraMap K L).injective) := ⟨rfl⟩

/-- TODO: go mathlib -/
instance liesOver_self {K S : Type*} [CommRing K] [IsSimpleRing K] [PartialOrder S] [Semiring S]
    (v : AbsoluteValue K S) : v.LiesOver v := ⟨rfl⟩

/-- TODO: go mathlib -/
theorem liesOver_self_iff {K S : Type*} [CommRing K] [IsSimpleRing K] [PartialOrder S] [Semiring S]
    (v w : AbsoluteValue K S) : v.LiesOver w ↔ v = w := by
  simp [liesOver_iff]

/-- TODO: go mathlib -/
theorem LiesOver.trans {K L M S : Type*}
    [CommRing K] [CommRing L] [CommRing M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsSimpleRing K] [IsSimpleRing L] [Nontrivial M]
    [PartialOrder S] [Semiring S]
    (w : AbsoluteValue M S) (v : AbsoluteValue L S) (u : AbsoluteValue K S)
    [hwv : w.LiesOver v] [hvu : v.LiesOver u] : w.LiesOver u := by
  rw [liesOver_iff] at hwv hvu ⊢
  rw [← hvu, ← hwv]
  ext
  simp [← IsScalarTower.algebraMap_apply K L M]

/-! ### Criterion for a place to be non-archimedean -/

/-- An absolute value `v` is archimedean if and only if there exists `x` such that `v x ≤ 1`
and `v (x + 1) > 1`. -/
theorem not_isNonarchimedean_iff_exists_apply_le_one_and_apply_add_one_gt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    ¬IsNonarchimedean v ↔ ∃ x : K, v x ≤ 1 ∧ v (x + 1) > 1 := by
  simp only [IsNonarchimedean, le_sup_iff, not_forall, not_or, not_le, gt_iff_lt]
  refine ⟨fun ⟨x, y, h1, h2⟩ ↦ ?_, fun ⟨x, h1, h2⟩ ↦ ⟨x, 1, by linarith, by rwa [map_one]⟩⟩
  wlog hxy : v x ≤ v y generalizing x y
  · rw [add_comm x y] at h1 h2
    exact this y x h2 h1 (not_le.1 hxy).le
  rcases eq_or_ne y 0 with rfl | hy
  · simp at h1
  rw [← div_le_one (v.pos hy), ← map_div₀] at hxy
  replace h2 := div_lt_div_of_pos_right h2 (v.pos hy)
  rw [← map_div₀, div_self hy, map_one, ← map_div₀, add_div, div_self hy] at h2
  use x / y

/-- An archimedean absolute value is not trivial. -/
theorem isNontrivial_of_not_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (h : ¬IsNonarchimedean v) : v.IsNontrivial := by
  rw [not_isNonarchimedean_iff_exists_apply_le_one_and_apply_add_one_gt_one] at h
  obtain ⟨x, -, h⟩ := h
  use x + 1, (by rw [← v.ne_zero_iff]; linarith), h.ne'

/-- An absolute value `v` is non-archimedean if and only if `v(ℕ)` is bounded. -/
theorem isNonarchimedean_iff_exists_forall_apply_natCast_le
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∃ C : ℝ, ∀ n : ℕ, v n ≤ C := by
  refine ⟨fun h ↦ ⟨1, fun n ↦ h.apply_natCast_le_one_of_isNonarchimedean⟩, fun ⟨C, h⟩ ↦ ?_⟩
  by_contra H
  rw [not_isNonarchimedean_iff_exists_apply_le_one_and_apply_add_one_gt_one] at H
  obtain ⟨x, h1, h2⟩ := H
  have h3 (n : ℕ) : v (x + 1) ^ n ≤ (n + 1 :) * C := by
    rw [← map_pow, add_pow]
    refine (v.sum_le ..).trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), C := by
        gcongr with i _
        simp only [one_pow, mul_one, map_mul, map_pow]
        rw [← one_mul C, ← one_pow i]
        gcongr 2
        exact h _
      _ = _ := by simp
  have h4 := tendsto_exp_mul_div_rpow_atTop 1 _ (Real.log_pos h2)
  simp_rw [← Real.rpow_def_of_pos (zero_lt_one.trans h2), Real.rpow_one,
    Filter.tendsto_atTop_atTop] at h4
  specialize h4 (v (x + 1) * C + 1)
  obtain ⟨N, h4⟩ := h4
  obtain ⟨n, hn⟩ := exists_nat_gt N
  specialize h3 n
  specialize h4 (n + 1 :) (hn.le.trans (by simp))
  rw [le_div_iff₀ (by norm_cast; simp), Real.rpow_natCast, pow_succ'] at h4
  replace h3 := h4.trans (mul_le_mul_of_nonneg_left h3 (zero_lt_one.trans h2).le)
  rw [add_mul, ← mul_assoc, mul_right_comm _ _ C, one_mul, add_le_iff_nonpos_right] at h3
  norm_cast at h3

theorem isNonarchimedean_comp_iff
    {K L : Type*} [Field K] [Field L] (v : AbsoluteValue L ℝ) (f : K →+* L) :
    IsNonarchimedean (v.comp f.injective) ↔ IsNonarchimedean v := by
  have h (n : ℕ) : v.comp f.injective n = v n := show v (f n) = _ by simp
  simp_rw [isNonarchimedean_iff_exists_forall_apply_natCast_le, h]

theorem isNonarchimedean_iff_of_liesOver
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    IsNonarchimedean v ↔ IsNonarchimedean w := by
  rw [← LiesOver.comp_eq w v, isNonarchimedean_comp_iff]

theorem isNonarchimedean_iff_of_equiv
    {K : Type*} [Field K] {v w : AbsoluteValue K ℝ} (h0 : v ≈ w) :
    IsNonarchimedean v ↔ IsNonarchimedean w := by
  suffices ∀ v w : AbsoluteValue K ℝ, v ≈ w → IsNonarchimedean v → IsNonarchimedean w from
    ⟨this v w h0, this w v h0.symm⟩
  rintro v w (h0 : v.IsEquiv w) h
  rw [isEquiv_iff_exists_rpow_eq] at h0
  rw [isNonarchimedean_iff_exists_forall_apply_natCast_le] at h ⊢
  obtain ⟨C, h⟩ := h
  obtain ⟨c, hc, h0⟩ := h0
  refine ⟨C ^ c, fun n ↦ ?_⟩
  simp only [← congr($h0 n)]
  gcongr 1
  exact h n

theorem isNontrivial_of_isNontrivial_comp
    {K L : Type*} [Field K] [Field L] (v : AbsoluteValue L ℝ) {f : K →+* L}
    (h : (v.comp f.injective).IsNontrivial) : v.IsNontrivial := by
  rw [IsNontrivial] at h ⊢
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨f x, by rwa [map_ne_zero_iff f f.injective], h2⟩

theorem isNontrivial_iff_of_liesOver
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    v.IsNontrivial ↔ w.IsNontrivial := by
  rw [← LiesOver.comp_eq w v]
  refine ⟨w.isNontrivial_of_isNontrivial_comp, fun h ↦ ?_⟩
  contrapose! h
  have hn : IsNonarchimedean w := by
    rw [← w.isNonarchimedean_comp_iff (algebraMap K L)]
    contrapose! h
    exact isNontrivial_of_not_isNonarchimedean _ h
  rw [not_isNontrivial_iff] at h ⊢
  replace h (x) : w (algebraMap K L x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (h x hx).le
  suffices ∀ x : L, x ≠ 0 → ¬w x > 1 by
    intro x hx
    rcases lt_trichotomy (w x) 1 with hlt | heq | hgt
    · refine False.elim (this x⁻¹ (by simpa) ?_)
      rwa [map_inv₀, gt_iff_lt, one_lt_inv₀ (w.pos hx)]
    · exact heq
    · exact False.elim (this x hx hgt)
  intro x hx hgt
  have h1 := congr(w $(minpoly.aeval K x))
  have h2 := minpoly.monic (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  have h3 : w (∑ n ∈ Finset.range (minpoly K x).natDegree, (minpoly K x).coeff n • x ^ n) <
      w (x ^ (minpoly K x).natDegree) := by
    rcases (Finset.range (minpoly K x).natDegree).eq_empty_or_nonempty with h3 | h3
    · simp [h3, w.pos hx]
    · obtain ⟨i, hi, h4⟩ :=
        hn.finset_image_add_of_nonempty (fun n ↦ (minpoly K x).coeff n • x ^ n) h3
      refine h4.trans_lt ?_
      rw [Algebra.smul_def, map_mul]
      refine (mul_le_of_le_one_left (w.nonneg _) (h _)).trans_lt ?_
      simpa [pow_lt_pow_iff_right₀ hgt] using hi
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, h2.coeff_natDegree, one_smul,
    map_zero, hn.add_eq_max_of_ne h3.ne, max_eq_right h3.le] at h1
  simp [hx] at h1

/-- If a field `K` has an infinite place, then it must be of characteristic zero. -/
theorem charZero_of_not_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (h : ¬IsNonarchimedean v) : CharZero K := by
  rcases CharP.exists' K with hc | ⟨p, hp, hc⟩
  · exact hc
  refine False.elim (h ?_)
  rw [isNonarchimedean_iff_exists_forall_apply_natCast_le]
  use ((Finset.range (p + 1)).image (fun (n : ℕ) ↦ v n)).max' (by simp)
  intro n
  rw [CharP.cast_eq_mod]
  apply Finset.le_max'
  simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
  use n % p, (n.mod_lt hp.out.pos).le

/-- TODO: go mathlib -/
theorem _root_.Rat.AbsoluteValue.isNonarchimedean_padic (p : ℕ) [Fact p.Prime] :
    IsNonarchimedean (Rat.AbsoluteValue.padic p) := by
  rw [isNonarchimedean_iff_exists_forall_apply_natCast_le]
  exact ⟨1, fun n ↦ Rat.AbsoluteValue.padic_le_one p n⟩

/-- TODO: go mathlib -/
theorem _root_.Rat.AbsoluteValue.not_isNonarchimedean_real :
    ¬IsNonarchimedean Rat.AbsoluteValue.real := by
  simpa [isNonarchimedean_iff_exists_forall_apply_natCast_le] using exists_nat_gt

/-- **Gelfand-Tornheim theorem**: if a field `K` has an infinite place,
then there exists an embedding `K →+* ℂ` such that the absolute value is *equivalent* to
the usual absolute value `| |` on `ℂ`. Note that it is not necessary equal to `| |` as it is
in fact equal to `| | ^ c` for some `0 < c ≤ 1`.

Proof: see E. Artin, *Theory of Algebraic Numbers*, pp. 45 and 67. -/
theorem exists_ringHom_complex_of_not_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (h : ¬IsNonarchimedean v) :
    ∃ φ : K →+* ℂ, NumberField.place φ ≈ v := by
  have := v.charZero_of_not_isNonarchimedean h
  let vQ := v.comp (algebraMap ℚ K).injective
  have h1 : ¬IsNonarchimedean vQ := by rwa [isNonarchimedean_comp_iff]
  have h2 := vQ.isNontrivial_of_not_isNonarchimedean h1
  rcases Rat.AbsoluteValue.equiv_real_or_padic vQ h2 with h3 | h3
  · let R := vQ.Completion
    let Khat := v.Completion
    -- #check NormedAlgebra.Real.nonempty_algEquiv_or
    sorry
  obtain ⟨p, hp, h4⟩ := h3.exists
  have := Rat.AbsoluteValue.isNonarchimedean_padic p
  rw [← isNonarchimedean_iff_of_equiv h4] at this
  contradiction

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

theorem decompositionSubgroup_eq_top_of_not_isNontrivial
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬v.IsNontrivial) : v.decompositionSubgroup F = ⊤ := by
  rw [eq_top_iff]
  rintro σ -
  have (x : K) : v x ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (not_isNontrivial_apply h hx).le
  simp [mem_decompositionSubgroup_iff, this]

theorem apply_le_one_of_mem_decompositionSubgroup
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.decompositionSubgroup F) {x} (hx : v x ≤ 1) : v (σ x) ≤ 1 :=
  h.le ⟨x, hx, rfl⟩

theorem apply_le_one_iff_of_mem_decompositionSubgroup
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) {σ}
    (h : σ ∈ v.decompositionSubgroup F) {x} : v (σ x) ≤ 1 ↔ v x ≤ 1 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ v.apply_le_one_of_mem_decompositionSubgroup h hx⟩
  simpa using v.apply_le_one_of_mem_decompositionSubgroup (inv_mem h) hx

/-- An element is contained in the decomposition subgroup of `v` if and only if it is continuous
under the `v`-adic topology. (Is this correct?) -/
theorem mem_decompositionSubgroup_iff_continuous
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ) (σ) :
    σ ∈ v.decompositionSubgroup F ↔ Continuous (WithAbs.congr v v σ) := by
  sorry

/-- Our definition is the same as `ValuationSubring.decompositionSubgroup` for finite places. -/
theorem decompositionSubgroup_eq_of_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : IsNonarchimedean v) :
    v.decompositionSubgroup F = (v.toValuation h).valuationSubring.decompositionSubgroup F := by
  ext g
  simp only [mem_decompositionSubgroup_iff, MulAction.mem_stabilizer_iff, SetLike.ext'_iff]
  congr!

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Dᵥ(L/K) = Dᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem decompositionSubgroup_eq_comap
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.decompositionSubgroup K = (v.decompositionSubgroup F).comap
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  ext
  simp [mem_decompositionSubgroup_iff, Set.ext_iff,
    IntermediateField.restrictRestrictAlgEquivMapHom]

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) ≤ Iᵥ(L/F)`. -/
theorem map_decompositionSubgroup_le
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    (v.decompositionSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) ≤ v.decompositionSubgroup F := by
  simpa only [Subgroup.map_le_iff_le_comap] using (v.decompositionSubgroup_eq_comap F K).le

/-- Decomposition subgroup for an infinite place is either trivial or `ℤ/2ℤ`. (Is this correct?) -/
theorem card_decompositionSubgroup_dvd_two_of_not_isNonarchimedean
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬IsNonarchimedean v) :
    Nat.card (v.decompositionSubgroup F) ∣ 2 := by
  sorry

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

theorem inertiaSubgroup_eq_bot_of_not_isNontrivial
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (v : AbsoluteValue K ℝ)
    (h : ¬v.IsNontrivial) : v.inertiaSubgroup F = ⊥ := by
  rw [eq_bot_iff]
  rintro σ hσ
  rw [Subgroup.mem_bot]
  ext x
  rw [v.mem_inertiaSubgroup_iff_of_isNonarchimedean F (by
    contrapose! h; exact isNontrivial_of_not_isNonarchimedean _ h)] at hσ
  replace hσ := hσ.2 x <| by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (not_isNontrivial_apply h hx).le
  replace hσ : σ x - x = 0 := by
    contrapose! hσ
    exact (not_isNontrivial_apply h hσ).ge
  simpa [sub_eq_zero] using hσ

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

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) = Iᵥ(L/F) ⊓ Gal(L/K)`. -/
theorem inertiaSubgroup_eq_comap
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    v.inertiaSubgroup K = (v.inertiaSubgroup F).comap
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) := by
  ext
  simp only [mem_inertiaSubgroup_iff, Subgroup.mem_comap]
  congr! <;> (ext; simp [IntermediateField.restrictRestrictAlgEquivMapHom])

/-- If `L / K / F` is an extension tower with `L / F` Galois, `v` is a place of `L`, then
`Iᵥ(L/K) ≤ Iᵥ(L/F)`. -/
theorem map_inertiaSubgroup_le
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) :
    (v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L) ≤ v.inertiaSubgroup F := by
  simpa only [Subgroup.map_le_iff_le_comap] using (v.inertiaSubgroup_eq_comap F K).le

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
(`0` means infinite). Later we will show that this depends only on the place of `K` below `v`,
and is independent of the choice of `L` (`AbsoluteValue.ramificationIdx_spec`). -/
noncomputable def ramificationIdxOfIsScalarTower
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue L ℝ) : ℕ :=
    ((v.inertiaSubgroup K).map
      (IntermediateField.restrictRestrictAlgEquivMapHom F L K L)).relIndex (v.inertiaSubgroup F)

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

/-- If `K / F` is an algebraic extension, then any place `v` of `F` can be extended to `K`.
(Is this correct?) -/
theorem exists_liesOver
    {F : Type*} (K : Type*) [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue F ℝ) : ∃ w : AbsoluteValue K ℝ, w.LiesOver v := by
  sorry

/-- If `K / F` is an algebraic extension, `v` is a place of `K`, then the
ramification index of `v` for `K / F` is defined to be the ramification index of `w`
for `K / F`, where `w` is any extension of `v` to the algebraic closure of `K`. -/
noncomputable def ramificationIdx
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (v : AbsoluteValue K ℝ) : ℕ :=
  (v.exists_liesOver (AlgebraicClosure K)).choose.ramificationIdxOfIsScalarTower F K

/-- (Is this correct?) -/
theorem ramificationIdx_spec
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K]
    {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [Normal F L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    haveI := Algebra.IsAlgebraic.tower_bot F K L
    v.ramificationIdx F = w.ramificationIdxOfIsScalarTower F K := by
  sorry

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

end AbsoluteValue
