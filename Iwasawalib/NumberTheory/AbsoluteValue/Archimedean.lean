/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.NumberTheory.Ostrowski

@[expose] public section

/-!

# Basic properties of archimedean and non-archimedean `ℝ`-valued `AbsoluteValue`

Consider an `ℝ`-valued `AbsoluteValue`.

- It is called finite, if it is non-archimedean (`IsNonarchimedean`).
- It is called archimedean or infinite, if it is not non-archimedean.

Main results:

- `AbsoluteValue.not_isNonarchimedean_iff_exists_apply_le_one_and_apply_add_one_gt_one`:
  an absolute value `v` is archimedean if and only if there exists `x` such that `v x ≤ 1`
  and `v (x + 1) > 1`.
- `AbsoluteValue.isNonarchimedean_iff_exists_forall_apply_natCast_le`:
  an absolute value `v` is non-archimedean if and only if `v(ℕ)` is bounded.
- `AbsoluteValue.charZero_of_not_isNonarchimedean`:
  if a field has an infinite place, then it must be of characteristic zero.

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

/-- An absolute value `v` is non-archimedean if and only if `v(ℕ)` is bounded by one. -/
theorem isNonarchimedean_iff_forall_apply_natCast_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∀ n : ℕ, v n ≤ 1 :=
  ⟨fun h _ ↦ h.apply_natCast_le_one_of_isNonarchimedean, fun h ↦
    v.isNonarchimedean_iff_exists_forall_apply_natCast_le.2 ⟨1, h⟩⟩

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
@[simp]
theorem _root_.Rat.AbsoluteValue.isNonarchimedean_padic (p : ℕ) [Fact p.Prime] :
    IsNonarchimedean (Rat.AbsoluteValue.padic p) := by
  rw [isNonarchimedean_iff_exists_forall_apply_natCast_le]
  exact ⟨1, fun n ↦ Rat.AbsoluteValue.padic_le_one p n⟩

/-- TODO: go mathlib -/
@[simp]
theorem _root_.Rat.AbsoluteValue.not_isNonarchimedean_real :
    ¬IsNonarchimedean Rat.AbsoluteValue.real := by
  simpa [isNonarchimedean_iff_exists_forall_apply_natCast_le] using exists_nat_gt

/-- TODO: go mathlib -/
@[simp]
theorem _root_.Rat.AbsoluteValue.isNontrivial_padic (p : ℕ) [Fact p.Prime] :
    (Rat.AbsoluteValue.padic p).IsNontrivial := by
  use p
  simp [‹Fact p.Prime›.out.ne_zero, ‹Fact p.Prime›.out.ne_one]

/-- TODO: go mathlib -/
@[simp]
theorem _root_.Rat.AbsoluteValue.isNontrivial_real :
    Rat.AbsoluteValue.real.IsNontrivial := by
  use 2
  simp

/-- TODO: go mathlib -/
theorem _root_.Rat.AbsoluteValue.equiv_real_of_not_isNonarchimedean
    (v : AbsoluteValue ℚ ℝ) (h : ¬IsNonarchimedean v) : v ≈ Rat.AbsoluteValue.real := by
  rcases Rat.AbsoluteValue.equiv_real_or_padic v
    (v.isNontrivial_of_not_isNonarchimedean h) with hv | hv
  · exact hv
  · rw [isNonarchimedean_iff_of_equiv hv.exists.choose_spec.choose_spec] at h
    convert False.elim <| h <| Rat.AbsoluteValue.isNonarchimedean_padic _

/-- TODO: go mathlib -/
theorem _root_.Rat.AbsoluteValue.equiv_padic_of_isNonarchimedean
    (v : AbsoluteValue ℚ ℝ) (h0 : v.IsNontrivial) (h : IsNonarchimedean v) :
    ∃! p, ∃ (_ : Fact p.Prime), v ≈ Rat.AbsoluteValue.padic p := by
  rcases Rat.AbsoluteValue.equiv_real_or_padic v h0 with hv | hv
  · rw [isNonarchimedean_iff_of_equiv hv] at h
    exact False.elim <| Rat.AbsoluteValue.not_isNonarchimedean_real h
  · exact hv

/-- A non-archimedean absolute value is a valuation. -/
@[simps]
def toValuation
    {R : Type*} [Ring R] [Nontrivial R] (v : AbsoluteValue R ℝ) (h : IsNonarchimedean v) :
    Valuation R NNReal where
  toFun x := ⟨v x, v.nonneg' x⟩
  map_zero' := by simp only [AbsoluteValue.map_zero]; rfl
  map_one' := by simp only [AbsoluteValue.map_one]; rfl
  map_mul' x y := by simp only [AbsoluteValue.map_mul]; rfl
  map_add_le_max' x y := h x y

/-- If `v` is an `ℝ`-valued absolute value, `c` is a positive real number,
either `c ≤ 1` or `v` is non-archimedean, then `v ^ c` is also an absolute value. -/
@[simps apply]
noncomputable def rpowOfLeOneOrIsNonarchimedean {R : Type*} [Semiring R]
    (v : AbsoluteValue R ℝ)
    (c : ℝ) (h1 : 0 < c) (h2 : c ≤ 1 ∨ IsNonarchimedean v) : AbsoluteValue R ℝ where
  toFun x := v x ^ c
  map_mul' x y := by rw [map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) c
  eq_zero' x := by rw [Real.rpow_eq_zero (v.nonneg x) h1.ne', v.eq_zero]
  add_le' x y := by
    rcases h2 with h2 | h2
    · exact (Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) h1.le).trans
        (Real.rpow_add_le_add_rpow (v.nonneg x) (v.nonneg y) h1.le h2)
    · exact (Real.rpow_le_rpow (v.nonneg _) (h2 x y) h1.le).trans_eq
        (Real.rpow_max (v.nonneg x) (v.nonneg y) h1.le) |>.trans
        (max_le_add_of_nonneg (by positivity) (by positivity))

/-! ### Retrieving the `p` for a `p`-adic valuation -/

/-- If `v` is an `ℝ`-valued absolute value on a characteristic zero field, then
`AbsoluteValue.adic v` is the natural number `p` such that either:

- `p` is a prime and the restriction of `v` to `ℚ` is equivalent to the usual `p`-adic valuation;
- `p = 1` and the restriction of `v` to `ℚ` is equivalent to the usual `∞`-adic valuation;
- `p = 0` and the restriction of `v` to `ℚ` is trivial. -/
noncomputable def adic {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ) : ℕ :=
  open scoped Classical in
  if nontriv : (v.comp (algebraMap ℚ K).injective).IsNontrivial then
    if h : v.comp (algebraMap ℚ K).injective ≈ Rat.AbsoluteValue.real then
      1
    else
      (Rat.AbsoluteValue.equiv_real_or_padic _ nontriv).resolve_left h |>.exists.choose
  else
    0

theorem adic_eq_of_liesOver
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    v.adic = w.adic := by
  have : v.comp (algebraMap ℚ K).injective = w.comp (algebraMap ℚ L).injective := by
    ext
    simp [← LiesOver.comp_eq w v]
  simp only [adic]; congr!

theorem adic_eq_of_equiv
    {K : Type*} [Field K] [CharZero K] {v w : AbsoluteValue K ℝ} (h0 : v ≈ w) :
    v.adic = w.adic := by
  replace h0 := IsEquiv.comp h0 (algebraMap ℚ K).injective
  have := h0.isNontrivial_congr
  have : ∀ u, v.comp (algebraMap ℚ K).injective ≈ u ↔ w.comp (algebraMap ℚ K).injective ≈ u :=
    fun u ↦ ⟨fun h ↦ h0.symm.trans h, fun h ↦ h0.trans h⟩
  simp only [adic]; grind

theorem adic_eq_one_iff {K : Type*} [Field K] [CharZero K] {v : AbsoluteValue K ℝ} :
    v.adic = 1 ↔ ¬IsNonarchimedean v := by
  rw [← isNonarchimedean_iff_of_liesOver (v.comp (algebraMap ℚ K).injective) v, adic]
  split_ifs with h1 h2
  · simp [isNonarchimedean_iff_of_equiv h2]
  · have h3 := (Rat.AbsoluteValue.equiv_real_or_padic _ h1).resolve_left h2 |>.exists
    simp [isNonarchimedean_iff_of_equiv h3.choose_spec.choose_spec,
      h3.choose_spec.choose.out.ne_one]
  · contrapose h1
    exact isNontrivial_of_not_isNonarchimedean _ (by simpa using h1)

theorem adic_eq_zero_iff {K : Type*} [Field K] [CharZero K] {v : AbsoluteValue K ℝ} :
    v.adic = 0 ↔ ¬(v.comp (algebraMap ℚ K).injective).IsNontrivial := by
  rw [adic]
  split_ifs with h1 h2
  · simp [IsEquiv.isNontrivial_congr h2]
  · have h3 := (Rat.AbsoluteValue.equiv_real_or_padic _ h1).resolve_left h2 |>.exists
    simp [h1, h3.choose_spec.choose.out.ne_zero]
  · simp [h1]

theorem adic_eq_zero_iff_of_isAlgebraic {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] {v : AbsoluteValue K ℝ} :
    v.adic = 0 ↔ ¬v.IsNontrivial := by
  rw [adic_eq_zero_iff, isNontrivial_iff_of_liesOver (v.comp (algebraMap ℚ K).injective) v]

theorem prime_adic {K : Type*} [Field K] [CharZero K] {v : AbsoluteValue K ℝ}
    (h1 : (v.comp (algebraMap ℚ K).injective).IsNontrivial) (h2 : IsNonarchimedean v) :
    v.adic.Prime := by
  rw [← isNonarchimedean_iff_of_liesOver (v.comp (algebraMap ℚ K).injective) v] at h2
  rw [adic, dif_pos h1]
  split_ifs with h3
  · simp [isNonarchimedean_iff_of_equiv h3] at h2
  · exact (Rat.AbsoluteValue.equiv_real_or_padic _ h1).resolve_left h3
      |>.exists.choose_spec.choose.out

theorem prime_adic_of_isAlgebraic {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {v : AbsoluteValue K ℝ} (h1 : v.IsNontrivial) (h2 : IsNonarchimedean v) :
    v.adic.Prime :=
  v.prime_adic (by rwa [isNontrivial_iff_of_liesOver (v.comp (algebraMap ℚ K).injective) v]) h2

@[simp]
theorem _root_.Rat.AbsoluteValue.adic_padic (p : ℕ) [Fact p.Prime] :
    (Rat.AbsoluteValue.padic p).adic = p := by
  have h1 : ¬Rat.AbsoluteValue.padic p ≈ Rat.AbsoluteValue.real :=
    fun h ↦ Rat.AbsoluteValue.not_real_isEquiv_padic p h.symm
  simp only [adic, Algebra.algebraMap_self, comp_id, Rat.AbsoluteValue.isNontrivial_padic,
    ↓reduceDIte, h1]
  apply Rat.AbsoluteValue.equiv_real_or_padic (Rat.AbsoluteValue.padic p) (by simp)
    |>.resolve_left h1 |>.unique
  · grind
  · exact ⟨‹_›, .rfl⟩

@[simp]
theorem _root_.Rat.AbsoluteValue.adic_real :
    Rat.AbsoluteValue.real.adic = 1 := by
  simp [adic]

end AbsoluteValue
