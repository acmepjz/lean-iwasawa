/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.Analysis.AbsoluteValue.Archimedean

@[expose] public section

/-!

# Normalization of an `ℝ`-valued `AbsoluteValue` over a characteristic zero field

-/

namespace AbsoluteValue

variable {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)

/-! ### Typeclass asserting that an absolute value is normalized -/

/-- If `v` is an `ℝ`-valued `AbsoluteValue` over a characteristic zero field, then
`AbsoluteValue.IsNormalized v` is a typeclass asserting that `v` is normalized, in the sense that
the restriction of `v` to `ℚ` is equal to the usual `∞`-adic valuation or `p`-adic valuation
on `ℚ`. In particular such `v` is non-trivial. -/
@[mk_iff]
class inductive IsNormalized (v : AbsoluteValue K ℝ) : Prop
| of_archimedean (h : v.comp (algebraMap ℚ K).injective = Rat.AbsoluteValue.real)
| of_nonarchimedean (p : ℕ) [Fact p.Prime]
    (h : v.comp (algebraMap ℚ K).injective = Rat.AbsoluteValue.padic p)

theorem isNontrivial_of_isNormalized' [v.IsNormalized] :
    (v.comp (algebraMap ℚ K).injective).IsNontrivial := by
  cases ‹v.IsNormalized› with
  | of_archimedean hv | of_nonarchimedean p hv =>
    simp [hv]

theorem isNontrivial_of_isNormalized [v.IsNormalized] : v.IsNontrivial :=
  v.isNontrivial_of_isNontrivial_comp v.isNontrivial_of_isNormalized'

/-- To check if an absolute value is normalized, one only needs to check it on natural numbers. -/
theorem isNormalized_iff_forall_apply_natCast_eq :
    v.IsNormalized ↔ (∀ n : ℕ, v n = n) ∨
      ∃ (p : ℕ) (_ : Fact p.Prime), ∀ n : ℕ, v n = padicNorm p n := by
  have h1 (n : ℕ) : (n : ℝ) = (|(n : ℚ)| :) := by simp
  have h2 (n : ℕ) : v n = v.comp (algebraMap ℚ K).injective n := by simp
  simp_rw [← Rat.AbsoluteValue.padic_eq_padicNorm, h2]
  conv => enter [2, 1, n, 2]; rw [h1, ← Rat.AbsoluteValue.real_eq_abs]
  simp_rw [Rat.AbsoluteValue.eq_on_nat_iff_eq, isNormalized_iff]

theorem isNormalized_iff_of_liesOver
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    v.IsNormalized ↔ w.IsNormalized := by
  have : v.comp (algebraMap ℚ K).injective = w.comp (algebraMap ℚ L).injective := by
    ext
    simp [← LiesOver.comp_eq w v]
  simp_rw [isNormalized_iff]
  congr!

theorem IsEquiv.eq_of_isNormalized {v w : AbsoluteValue K ℝ} (h : v.IsEquiv w)
    [v.IsNormalized] [w.IsNormalized] : v = w := by
  obtain ⟨c, h1, h2⟩ := isEquiv_iff_exists_rpow_eq.1 h
  cases ‹v.IsNormalized› with
  | of_archimedean hv =>
    cases ‹w.IsNormalized› with
    | of_archimedean hw =>
      rw [← hw] at hv
      have : (2 : ℝ) ^ c = 2 ^ (1 : ℝ) := by
        replace h2 := congr($(h2) 2)
        replace hv := congr($(hv) 2)
        replace hw := congr($(hw) 2)
        simp_all
      rw [Real.rpow_right_inj (by simp) (by simp)] at this
      simpa [this] using h2
    | of_nonarchimedean p hw =>
      have := Rat.AbsoluteValue.not_isNonarchimedean_real
      simp [← hv, isNonarchimedean_iff_of_equiv (h.comp _), hw] at this
  | of_nonarchimedean p hv =>
    cases ‹w.IsNormalized› with
    | of_archimedean hw =>
      have := Rat.AbsoluteValue.not_isNonarchimedean_real
      simp [← hw, ← isNonarchimedean_iff_of_equiv (h.comp _), hv] at this
    | of_nonarchimedean q hw =>
      have hqp : q = p := by
        have := h.comp (algebraMap ℚ K).injective
        rw [hv, hw] at this
        have := adic_eq_of_equiv this.symm
        simpa using this
      have : (p : ℝ)⁻¹ ^ c = (p : ℝ)⁻¹ ^ (1 : ℝ) := by
        replace h2 := congr($(h2) p)
        replace hv := congr($(hv) p)
        replace hw := congr($(hw) p)
        simp_all
      rw [Real.rpow_right_inj (by simp [‹Fact p.Prime›.out.pos])
        (by simp [‹Fact p.Prime›.out.ne_one])] at this
      simpa [this] using h2

theorem isEquiv_iff_eq_of_isNormalized {v w : AbsoluteValue K ℝ}
    [v.IsNormalized] [w.IsNormalized] : v.IsEquiv w ↔ v = w :=
  ⟨fun h ↦ h.eq_of_isNormalized, by rintro rfl; exact .rfl⟩

instance _root_.Rat.AbsoluteValue.isNormalized_real : Rat.AbsoluteValue.real.IsNormalized :=
  .of_archimedean (by simp)

instance _root_.Rat.AbsoluteValue.isNormalized_padic (p : ℕ) [Fact p.Prime] :
    (Rat.AbsoluteValue.padic p).IsNormalized :=
  .of_nonarchimedean p (by simp)

theorem _root_.Rat.AbsoluteValue.eq_real_or_padic_of_isNormalized
    (v : AbsoluteValue ℚ ℝ) [v.IsNormalized] :
    v = Rat.AbsoluteValue.real ∨ ∃! p, ∃ (_ : Fact p.Prime), v = Rat.AbsoluteValue.padic p := by
  have : v.IsEquiv _ ∨ ∃! p, ∃ (_ : Fact p.Prime), v.IsEquiv (Rat.AbsoluteValue.padic p) :=
    Rat.AbsoluteValue.equiv_real_or_padic v v.isNontrivial_of_isNormalized
  simpa only [isEquiv_iff_eq_of_isNormalized] using this

theorem _root_.Rat.AbsoluteValue.eq_real_of_not_isNonarchimedean_of_isNormalized
    (v : AbsoluteValue ℚ ℝ) (h : ¬IsNonarchimedean v) [v.IsNormalized] :
    v = Rat.AbsoluteValue.real := by
  have : v.IsEquiv _ := Rat.AbsoluteValue.equiv_real_of_not_isNonarchimedean v h
  simpa only [isEquiv_iff_eq_of_isNormalized] using this

theorem _root_.Rat.AbsoluteValue.eq_padic_of_isNonarchimedean_of_isNormalized
    (v : AbsoluteValue ℚ ℝ) (h : IsNonarchimedean v) [v.IsNormalized] :
    ∃! p, ∃ (_ : Fact p.Prime), v = Rat.AbsoluteValue.padic p := by
  have : ∃! p, ∃ (_ : Fact p.Prime), v.IsEquiv (Rat.AbsoluteValue.padic p) :=
    Rat.AbsoluteValue.equiv_padic_of_isNonarchimedean v v.isNontrivial_of_isNormalized h
  simpa only [isEquiv_iff_eq_of_isNormalized] using this

theorem apply_adic_eq_inv_of_isNormalized [v.IsNormalized] : v v.adic = (v.adic : ℝ)⁻¹ := by
  have (n : ℕ) : v n = v.comp (algebraMap ℚ K).injective n := by simp
  simp_rw [← adic_eq_of_liesOver (v.comp (algebraMap ℚ K).injective) v, this]
  cases ‹v.IsNormalized› with
  | of_archimedean hv | of_nonarchimedean p hv =>
    simp [hv]

/-! ### Normalization of an absolute value -/

/-- The exponent `c` which makes `v ^ c` normalized. -/
noncomputable def normalizationExponent : ℝ :=
  open scoped Classical in
  if nontriv : (v.comp (algebraMap ℚ K).injective).IsNontrivial then
    if h : v.comp (algebraMap ℚ K).injective ≈ Rat.AbsoluteValue.real then
      1 / (isEquiv_iff_exists_rpow_eq.1 h.symm).choose
    else
      haveI h2 := (Rat.AbsoluteValue.equiv_real_or_padic _ nontriv).resolve_left h
        |>.exists.choose_spec.choose_spec
      1 / (isEquiv_iff_exists_rpow_eq.1 h2.symm).choose
  else
    1

theorem normalizationExponent_pos : 0 < v.normalizationExponent := by
  rw [normalizationExponent]
  split_ifs
  · rw [one_div_pos]; grind
  · rw [one_div_pos]; grind
  · simp

-- AI slop
omit [CharZero K] in
private lemma normalization_triangle
    (s : ℝ) (hs : 0 < s) (h_nat : ∀ n : ℕ, v n = n ^ s) (x y : K) :
    v (x + y) ^ (1 / s) ≤ v x ^ (1 / s) + v y ^ (1 / s) := by
  have tendsto_root_succ_nat : Filter.Tendsto (fun n : ℕ ↦ ((n + 1) : ℝ) ^ (1 / (n : ℝ)))
      .atTop (nhds 1) := by
    suffices h_eq : Filter.Tendsto (fun n : ℕ ↦
        (n : ℝ) ^ (1 / (n : ℝ)) * (1 + 1 / (n : ℝ)) ^ (1 / (n : ℝ))) .atTop (nhds 1) by
      apply h_eq.congr'
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [← Real.mul_rpow (by positivity) (by positivity), mul_add,
        mul_one_div_cancel (by positivity), mul_one]
    have h1 : Filter.Tendsto (fun x : ℝ ↦ x ^ (1 / x)) .atTop (nhds 1) := by
      simpa using tendsto_rpow_div_mul_add 1 1 0
    convert (h1.comp tendsto_natCast_atTop_atTop).mul
      ((tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).rpow
        tendsto_one_div_atTop_nhds_zero_nat _ ) using 2 <;> norm_num
  have h1 (n : ℕ) : v (x + y) ^ n ≤ (n + 1) * (v x ^ (1 / s) + v y ^ (1 / s)) ^ (n * s) := by
    have h_expand : v (x + y) ^ n ≤ ∑ k ∈ Finset.range (n + 1),
        Nat.choose n k ^ s * v x ^ (k / s * s) * v y ^ ((n - k :) / s * s) := by
      simp_rw [div_mul_cancel₀ _ hs.ne', Real.rpow_natCast]
      rw [← v.map_pow, add_pow]
      refine (v.sum_le _ _).trans ?_
      gcongr 1 with k hk
      apply Eq.le
      simp only [v.map_mul, v.map_pow, h_nat]
      ring
    have h_bound : ∀ k ∈ Finset.range (n + 1),
        Nat.choose n k ^ s * v x ^ (k / s * s) * v y ^ ((n - k :) / s * s) ≤
          (v x ^ (1 / s) + v y ^ (1 / s)) ^ (n * s) := by
      intro k hk
      simp_rw [Real.rpow_mul (v.nonneg _)]
      rw [Real.rpow_mul (by positivity), ← Real.mul_rpow (by positivity) (by positivity),
        ← Real.mul_rpow (by positivity) (by positivity)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      rw [Real.rpow_natCast, add_pow]
      refine (Finset.single_le_sum (fun _ _ ↦ by positivity) hk).trans_eq' ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div, inv_mul_eq_div,
        inv_mul_eq_div]
      ring
    refine h_expand.trans (Finset.sum_le_sum h_bound) |>.trans_eq ?_
    simp
  have h_root (n : ℕ) (hn : n > 0) :
      v (x + y) ≤ (n + 1 : ℝ) ^ (1 / (n : ℝ)) * (v x ^ (1 / s) + v y ^ (1 / s)) ^ s := by
    have := Real.rpow_le_rpow (z := (n : ℝ)⁻¹) (by positivity) (h1 n) (by positivity)
    rwa [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_right_comm,
      mul_inv_cancel₀ (by positivity), Real.rpow_one, one_mul, ← one_div] at this
  have h_limit : v (x + y) ≤ (v x ^ (1 / s) + v y ^ (1 / s)) ^ s :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa using tendsto_root_succ_nat.mul_const _)
      (Filter.eventually_atTop.2 ⟨1, h_root⟩)
  refine (Real.rpow_le_rpow (by positivity) h_limit (by positivity)).trans_eq ?_
  rw [← Real.rpow_mul (by positivity), mul_one_div_cancel (by positivity), Real.rpow_one]

/-- The normalization of an absolute value. -/
@[simps apply]
noncomputable def normalization : AbsoluteValue K ℝ where
  toFun x := v x ^ v.normalizationExponent
  map_mul' x y := by rw [map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) _
  eq_zero' x := by rw [Real.rpow_eq_zero (v.nonneg x) v.normalizationExponent_pos.ne', v.eq_zero]
  add_le' x y := by
    rw [normalizationExponent]
    split_ifs with nontriv h
    · obtain ⟨h1, h2⟩ := (isEquiv_iff_exists_rpow_eq.1 h.symm).choose_spec
      refine v.normalization_triangle _ h1 (fun n ↦ ?_) x y
      simpa using congr($(h2.symm) n)
    · have h2 := ((Rat.AbsoluteValue.equiv_real_or_padic _ nontriv).resolve_left h).exists
      obtain ⟨_, h3⟩ := h2.choose_spec
      have := Rat.AbsoluteValue.isNonarchimedean_padic h2.choose
      rw [← isNonarchimedean_iff_of_equiv h3, isNonarchimedean_iff_of_liesOver _ v] at this
      exact (v.rpowOfLeOneOrIsNonarchimedean _ (by rw [one_div_pos]; grind) (.inr this)).add_le x y
    · simp [v.add_le]

theorem isEquiv_normalization : v.IsEquiv v.normalization := by
  rw [isEquiv_iff_exists_rpow_eq]
  use v.normalizationExponent, v.normalizationExponent_pos
  ext
  simp

theorem isNormalized_normalization_of_isNontrivial
    (hv : (v.comp (algebraMap ℚ K).injective).IsNontrivial) : v.normalization.IsNormalized := by
  simp_rw [isNormalized_iff_forall_apply_natCast_eq, normalization_apply, normalizationExponent,
    dif_pos hv]
  by_cases h : v.comp (algebraMap ℚ K).injective ≈ Rat.AbsoluteValue.real
  · left; simp_rw [dif_pos h]
    obtain ⟨h1, h2⟩ := (isEquiv_iff_exists_rpow_eq.1 h.symm).choose_spec
    intro n
    replace h2 := congr($(h2.symm) n)
    simp_all [← Real.rpow_mul (show 0 ≤ (n : ℝ) by simp), mul_inv_cancel₀ h1.ne']
  · right; simp_rw [dif_neg h]
    have h0 := (Rat.AbsoluteValue.equiv_real_or_padic _ hv).resolve_left h |>.exists
    obtain ⟨h1, h2⟩ := h0.choose_spec
    obtain ⟨h3, h4⟩ := (isEquiv_iff_exists_rpow_eq.1 h2.symm).choose_spec
    use h0.choose, h1
    intro n
    replace h4 := congr($(h4.symm) n)
    simp_all [← Real.rpow_mul (show 0 ≤ ((padicNorm h0.choose n :) : ℝ) by simp [padicNorm.nonneg]),
      mul_inv_cancel₀ h3.ne']

theorem isNormalized_normalization_of_isNontrivial_of_isAlgebraic
    (hv : v.IsNontrivial) [Algebra.IsAlgebraic ℚ K] : v.normalization.IsNormalized :=
  v.isNormalized_normalization_of_isNontrivial <| by
    rwa [isNontrivial_iff_of_liesOver (v.comp (algebraMap ℚ K).injective) v]

end AbsoluteValue
