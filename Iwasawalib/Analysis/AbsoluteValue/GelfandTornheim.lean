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

end AbsoluteValue
