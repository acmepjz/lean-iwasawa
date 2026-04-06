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

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-! ### Typeclass asserting that an absolute value is normalized -/

/-- `AbsoluteValue.IsNormalized v` is a typeclass asserting that `v`
is a normalized absolute value, in our definition, it is either

- `v` is trivial;
- `v n = n` for all natural numbers `n`;
- there exists a prime `p` such that `v n = padicNorm p n` for all natural numbers `n`.

Note that for convenience, the definition has redundant assumptions. -/
class inductive IsNormalized (v : AbsoluteValue K ℝ) : Prop
| ofTrivial (htriv : ¬v.IsNontrivial)
| ofArchimedean (hnontriv : v.IsNontrivial) (harch : ¬IsNonarchimedean v)
    (h : ∀ n : ℕ, v n = n)
| ofNonarchimedean (hnontriv : v.IsNontrivial) (hnonarch : IsNonarchimedean v)
    (p : ℕ) [Fact p.Prime] (h : ∀ n : ℕ, v n = padicNorm p n)

theorem IsEquiv.eq_of_isNormalized [CharZero K] {v w : AbsoluteValue K ℝ} (h : v.IsEquiv w)
    [v.IsNormalized] [w.IsNormalized] : v = w := by
  obtain ⟨c, h1, h2⟩ := isEquiv_iff_exists_rpow_eq.1 h
  cases ‹v.IsNormalized› with
  | ofTrivial hv =>
    have hw := hv
    rw [h.isNontrivial_congr] at hw
    ext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [not_isNontrivial_apply hv hx, not_isNontrivial_apply hw hx]
  | ofArchimedean hnontriv_v harch_v hv =>
    cases ‹w.IsNormalized› with
    | ofTrivial hw =>
      rw [h.isNontrivial_congr] at hnontriv_v
      contradiction
    | ofArchimedean hnontriv_w harch_w hw =>
      have := congr($(h2) 2)
      simp only [show v 2 = 2 by exact_mod_cast hv 2, show w 2 = 2 by exact_mod_cast hw 2] at this
      nth_rw 2 [← Real.rpow_one (2 : ℝ)] at this
      rw [Real.rpow_right_inj (by simp) (by simp)] at this
      simpa [this] using h2
    | ofNonarchimedean hnontriv_w hnonarch_w p hw =>
      rw [isNonarchimedean_iff_of_equiv h] at harch_v
      contradiction
  | ofNonarchimedean hnontriv_v hnonarch_v p hv =>
    cases ‹w.IsNormalized› with
    | ofTrivial hw =>
      rw [h.isNontrivial_congr] at hnontriv_v
      contradiction
    | ofArchimedean hnontriv_w harch_w hw =>
      rw [isNonarchimedean_iff_of_equiv h] at hnonarch_v
      contradiction
    | ofNonarchimedean hnontriv_w hnonarch_w q hw =>
      specialize hw p
      simp only [← congr($(h2) p), hv] at hw
      have hinj := fun y z ↦ @Real.rpow_right_inj (p : ℝ)⁻¹ y z (by simp [‹Fact p.Prime›.out.pos])
        fun H ↦ by simp [‹Fact p.Prime›.out.ne_one] at H
      have hqp : q = p := by
        by_contra! hqp
        simp only [padicNorm.padicNorm_of_prime_of_ne hqp,
          padicNorm.padicNorm_p_of_prime, Rat.cast_inv, Rat.cast_natCast, Rat.cast_one] at hw
        rw [← Real.rpow_zero (p : ℝ)⁻¹, hinj] at hw
        exact h1.ne' hw
      simp only [hqp, padicNorm.padicNorm_p_of_prime, Rat.cast_inv, Rat.cast_natCast] at hw
      nth_rw 2 [← Real.rpow_one (p : ℝ)⁻¹] at hw
      rw [hinj] at hw
      ext x
      simpa [hw] using congr($(h2) x)

/-! ### Normalization of an absolute value -/

/-- The exponent `c` which makes `v ^ c` normalized. -/
noncomputable def normalizationExponent [CharZero K] : ℝ :=
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

theorem normalizationExponent_pos [CharZero K] :
    0 < v.normalizationExponent := by
  rw [normalizationExponent]
  split_ifs
  · rw [one_div_pos]; grind
  · rw [one_div_pos]; grind
  · simp

-- AI slop
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
noncomputable def normalization [CharZero K] : AbsoluteValue K ℝ where
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

end AbsoluteValue
