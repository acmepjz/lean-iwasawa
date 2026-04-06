/-
Copyright (c) 2026 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Iwasawalib.Analysis.AbsoluteValue.Archimedean
public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
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
