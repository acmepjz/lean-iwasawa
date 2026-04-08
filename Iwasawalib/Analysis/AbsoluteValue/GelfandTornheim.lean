/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.Analysis.AbsoluteValue.Normalization
public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

@[expose] public section

/-!

# Gelfand-Tornheim theorem

In this file the **Gelfand-Tornheim theorem**
(`AbsoluteValue.exists_ringHom_complex_of_not_isNonarchimedean`) is proved, that is,
if a field `K` has an infinite place,
then there exists an embedding `K →+* ℂ` such that the absolute value is *equivalent* to
the usual absolute value `| |` on `ℂ`.

-/

namespace AbsoluteValue

-- proof partially provided by AI
open Complex in
private lemma eq_norm_of_eq_norm_on_real
    (v : AbsoluteValue ℂ ℝ) (hv : ∀ x : ℝ, v x = ‖x‖) (x : ℂ) : v x = ‖x‖ := by
  have apply_I_eq_one : v I = 1 := by
    have : v I ^ 2 = 1 := by simp [← map_pow]
    nlinarith [v.nonneg I]
  have le_re_add_im (z : ℂ) : v z ≤ |z.re| + |z.im| := by
    nth_rw 1 [← re_add_im z]
    exact (v.add_le _ _).trans_eq (by simp [hv, apply_I_eq_one])
  have le_one_of_norm_le_one (z : ℂ) (hz : ‖z‖ ≤ 1) : v z ≤ 1 := by
    have hle (n : ℕ) : v z ^ n ≤ 2 := by
      rw [← map_pow, ← one_add_one_eq_two]
      refine (le_re_add_im _).trans
        (add_le_add ((abs_re_le_norm _).trans ?h) ((abs_im_le_norm _).trans ?h))
      simp [pow_le_one₀ (norm_nonneg z) hz]
    contrapose! hle
    exact pow_unbounded_of_one_lt _ hle
  have unit_eq_one (z : ℂ) (hz : ‖z‖ = 1) : v z = 1 := by
    refine (le_one_of_norm_le_one z hz.le).antisymm ?_
    have h2 := le_one_of_norm_le_one z⁻¹ (by simp [hz])
    simpa [inv_le_one_iff₀, show z ≠ 0 by intro H; simp [H] at hz] using h2
  by_cases hx : x = 0
  · simp [hx]
  · have decomp : x = (‖x‖ : ℂ) * (x / (‖x‖ : ℂ)) := by
      rw [mul_div_cancel₀ _ (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hx ))]
    nth_rw 1 [decomp]
    rw [map_mul, hv, unit_eq_one _ (by simpa), norm_norm, mul_one]

-- proof partially provided by AI
/-- **Gelfand-Tornheim theorem**: if a field `K` has a normalized archimedean absolute value,
then there exists an embedding `K →+* ℂ` such that the absolute value is equal to
the usual absolute value `| |` on `ℂ`. -/
theorem exists_ringHom_complex_of_not_isNonarchimedean_of_isNormalized
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ) (h : ¬IsNonarchimedean v)
    [v.IsNormalized] : ∃ φ : K →+* ℂ, NumberField.place φ = v := by
  let vQ := v.comp (algebraMap ℚ K).injective
  have : vQ.IsNormalized := by rwa [isNormalized_iff_of_liesOver vQ v]
  have vQ_eq_real := Rat.AbsoluteValue.eq_real_of_not_isNonarchimedean_of_isNormalized vQ <| by
    rwa [isNonarchimedean_comp_iff]
  -- Let `𝕂` be the completion of `K` and construct a map `i : ℝ →+* 𝕂`.
  let 𝕂 := v.Completion
  have norm_eq_v (a : K) : ‖algebraMap K 𝕂 a‖ = v a :=
    UniformSpace.Completion.norm_coe (WithAbs.toAbs v a)
  have norm_eq_vQ (a : ℚ) : ‖algebraMap ℚ 𝕂 a‖ = vQ a := norm_eq_v (algebraMap ℚ K a)
  have uniform_cont : UniformContinuous (algebraMap ℚ 𝕂) := by
    rw [Metric.uniformContinuous_iff]
    refine fun ε hε ↦ ⟨ε, hε, fun a b hab ↦ ?_⟩
    rw [dist_eq_norm] at hab
    rwa [dist_eq_norm, ← map_sub, norm_eq_vQ, vQ_eq_real]
  let i : ℝ →+* 𝕂 := IsDenseInducing.extendRingHom
    (show IsUniformInducing (algebraMap ℚ ℝ) from ⟨rfl⟩) Rat.denseRange_cast uniform_cont
  -- Prove some properties of `i`.
  have uniform_cont_i : UniformContinuous i := uniformContinuous_uniformly_extend
    (show IsUniformInducing (algebraMap ℚ ℝ) from ⟨rfl⟩) Rat.denseRange_cast uniform_cont
  have i_preserves_norm (r : ℝ) : ‖i r‖ = ‖r‖ := by
    suffices ∀ a : ℚ, ‖i a‖ = ‖a‖ by
      obtain ⟨q, -, -, hq⟩ := Real.exists_seq_rat_strictMono_tendsto r
      apply tendsto_nhds_unique ((uniform_cont_i.continuous.tendsto r).comp hq).norm
      simp only [Function.comp_apply, map_ratCast]
      convert hq.norm using 2 with x
      rw [← eq_ratCast (algebraMap ℚ 𝕂), norm_eq_vQ, vQ_eq_real]
      rfl
    intro a
    convert norm_eq_vQ a using 1
    · simp
    · rw [vQ_eq_real]; rfl
  -- Prove that `𝕂` is a normed `ℝ`-algebra.
  let := i.toAlgebra
  have norm_smul_eq (r : ℝ) (x : 𝕂) : ‖r • x‖ = ‖r‖ * ‖x‖ := by
    change ‖i r * x‖ = _
    rw [norm_mul, i_preserves_norm]
  let : NormedAlgebra ℝ 𝕂 := { norm_smul_le r x := (norm_smul_eq r x).le }
  -- By Gelfand-Mazur Theorem, `𝕂` is isomorphic to `ℝ` or `ℂ` as `ℝ`-algebra.
  -- We need to prove that such isomorphism preserves norm.
  rcases NormedAlgebra.Real.nonempty_algEquiv_or 𝕂 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have he : i = e.symm.toAlgHom.toRingHom := by
      rw [Algebra.ext_id _ e.symm.toAlgHom (Algebra.ofId ..)]
      rfl
    use (algebraMap ℝ ℂ).comp e.toAlgHom.toRingHom |>.comp (algebraMap K 𝕂)
    ext x
    simpa [i_preserves_norm, norm_eq_v] using congr(‖$(he) (e (algebraMap K 𝕂 x))‖)
  · let w := NumberField.place e.symm.toAlgHom.toRingHom
    have hw := eq_norm_of_eq_norm_on_real w fun x ↦ by
      have : e.symm x = i x := by
        change e.symm.toAlgHom (algebraMap ℝ ℂ x) = algebraMap ℝ 𝕂 x
        rw [AlgHom.commutes]
      simp [w, this, i_preserves_norm]
    use e.toAlgHom.toRingHom.comp (algebraMap K 𝕂)
    ext x
    simpa [w, norm_eq_v] using (hw (e (algebraMap K 𝕂 x))).symm

/-- **Gelfand-Tornheim theorem**: if a field `K` has an infinite place,
then there exists an embedding `K →+* ℂ` such that the absolute value is *equivalent* to
the usual absolute value `| |` on `ℂ`. Note that it is not necessary equal to `| |` as it is
in fact equal to `| | ^ c` for some `0 < c ≤ 1`. -/
theorem exists_ringHom_complex_of_not_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (h : ¬IsNonarchimedean v) :
    ∃ φ : K →+* ℂ, NumberField.place φ ≈ v := by
  have := v.charZero_of_not_isNonarchimedean h
  have := v.isNormalized_normalization_of_isNontrivial <| by
    apply isNontrivial_of_not_isNonarchimedean
    rwa [isNonarchimedean_iff_of_liesOver (v.comp (algebraMap ℚ K).injective) v]
  have := v.normalization.exists_ringHom_complex_of_not_isNonarchimedean_of_isNormalized <| by
    rwa [← isNonarchimedean_iff_of_equiv v.isEquiv_normalization]
  use this.choose
  simpa only [this.choose_spec] using v.isEquiv_normalization.symm

/-- Let `K / F` be a field extension, `v` and `w` are absolute values on `K` and `F`, respectively,
such that the restriction of `v` on `F` is equivalent to `w`, then there exists `v'`
equivalent to `v`, and which lies over `w`. -/
theorem exists_equiv_and_liesOver_of_comp_equiv
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue F ℝ) (h : v.comp (algebraMap F K).injective ≈ w) :
    ∃ v' : AbsoluteValue K ℝ, v' ≈ v ∧ v'.LiesOver w := by
  by_cases hn : IsNonarchimedean v
  · obtain ⟨c, hc, h1⟩ := isEquiv_iff_exists_rpow_eq.1 h
    refine ⟨v.rpowOfLeOneOrIsNonarchimedean c hc (.inr hn),
      .symm (isEquiv_iff_exists_rpow_eq.2 ⟨c, hc, rfl⟩), ?_⟩
    rw [liesOver_iff]
    ext x
    simpa using congr($h1 x)
  obtain ⟨φ, hφ⟩ := v.exists_ringHom_complex_of_not_isNonarchimedean hn
  obtain ⟨c, hc, h1⟩ := isEquiv_iff_exists_rpow_eq.1 hφ
  have hφ' := (IsEquiv.comp hφ (algebraMap F K).injective).trans h
  obtain ⟨c', hc', h2⟩ := isEquiv_iff_exists_rpow_eq.1 hφ'
  have hc'1 : c' ≤ 1 := by
    have h3 : 2 ^ c' = w 2 := by simpa [map_ofNat] using congr($h2 2)
    have h4 : w 2 ≤ 2 := by simpa [one_add_one_eq_two] using w.add_le 1 1
    rw [← h3] at h4
    contrapose! h4
    exact Real.self_lt_rpow_of_one_lt one_lt_two h4
  refine ⟨(NumberField.place φ).rpowOfLeOneOrIsNonarchimedean c' hc' (.inl hc'1),
    isEquiv_iff_exists_rpow_eq.2 ?_, ?_⟩
  · refine ⟨c'⁻¹ * c, by positivity, ?_⟩
    ext x
    rw [← h1, rpowOfLeOneOrIsNonarchimedean_apply, ← Real.rpow_mul ((NumberField.place φ).nonneg x),
      ← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul]
  · rw [liesOver_iff]
    ext x
    simpa using congr($h2 x)

end AbsoluteValue
