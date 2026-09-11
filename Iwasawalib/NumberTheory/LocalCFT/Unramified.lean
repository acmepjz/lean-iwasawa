/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.Inertia

@[expose] public section

/-!
# The cohomology of the local units at an unramified place

At an unramified place `w | v` of a finite Galois extension of number fields with cyclic
decomposition group, the units of the local integers `O_w` are cohomologically trivial:
`Ĥ⁰(D_w, O_wˣ) = Ĥ¹(D_w, O_wˣ) = 0` and `h(O_wˣ) = 1`.

The two inputs are supplied elsewhere: a `D_w`-fixed uniformizer, from
`Iwasawalib/NumberTheory/LocalCFT/DecompositionAction.lean`, and the residue field — finite by
`Iwasawalib/NumberTheory/LocalCFT/AdicResidueField.lean` and acted on faithfully by
`Iwasawalib/NumberTheory/LocalCFT/Inertia.lean`.  These statements therefore carry no hypothesis
beyond `e(w|v) = 1` and cyclicity of `D_w`.

## Main statements

* `NumberField.exists_smul_div_of_mulNorm_eq_one_adicCompletionIntegers`,
  `NumberField.isMulCoboundary₁_adicCompletionIntegers`: `Ĥ¹(D_w, O_wˣ) = 0`.
* `NumberField.exists_mulNorm_eq_of_smul_eq_adicCompletionIntegers`: `Ĥ⁰(D_w, O_wˣ) = 0`.
* `NumberField.herbrand_adicCompletionIntegers_units_eq_one`: `h(O_wˣ) = 1`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero

namespace NumberField

section Cohomology

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction Units.mulDistribMulActionRight

variable [Fintype (decompositionGroup K L w)]

/-- **`Ĥ¹(D_w, O_wˣ) = 0` at an unramified place.** -/
theorem exists_smul_div_of_mulNorm_eq_one_adicCompletionIntegers
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : decompositionGroup K L w} (hσ : ∀ d : decompositionGroup K L w,
      d ∈ Subgroup.zpowers σ)
    {x : (LocalCFT.integers (F := w.adicCompletion L))ˣ}
    (hx : CyclicCocycle.mulNorm (G := decompositionGroup K L w) x = 1) :
    ∃ y : (LocalCFT.integers (F := w.adicCompletion L))ˣ, σ • y / y = x := by
  haveI := faithfulSMul_residueField_integers v w h
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer_integers v w h
  exact LocalCFT.exists_smul_div_of_mulNorm_eq_one_of_finiteResidue hσ
    (valued_decomposition_smul_integers w) hπ hfix hx

/-- **Every multiplicative 1-cocycle `D_w → O_wˣ` is a coboundary at an unramified place.** -/
theorem isMulCoboundary₁_adicCompletionIntegers
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : decompositionGroup K L w} (hσ : ∀ d : decompositionGroup K L w,
      d ∈ Subgroup.zpowers σ)
    {f : decompositionGroup K L w → (LocalCFT.integers (F := w.adicCompletion L))ˣ}
    (hf : groupCohomology.IsMulCocycle₁ f) : groupCohomology.IsMulCoboundary₁ f := by
  haveI := faithfulSMul_residueField_integers v w h
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer_integers v w h
  exact LocalCFT.isMulCoboundary₁_of_finiteResidue hσ
    (valued_decomposition_smul_integers w) hπ hfix hf

/-- **`Ĥ⁰(D_w, O_wˣ) = 0` at an unramified place.** -/
theorem exists_mulNorm_eq_of_smul_eq_adicCompletionIntegers
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : decompositionGroup K L w} (hσ : ∀ d : decompositionGroup K L w,
      d ∈ Subgroup.zpowers σ)
    {x : (LocalCFT.integers (F := w.adicCompletion L))ˣ} (hx : σ • x = x) :
    ∃ y : (LocalCFT.integers (F := w.adicCompletion L))ˣ,
      CyclicCocycle.mulNorm (G := decompositionGroup K L w) y = x := by
  haveI := faithfulSMul_residueField_integers v w h
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer_integers v w h
  exact LocalCFT.exists_mulNorm_eq_of_smul_eq_of_finiteResidue hσ
    (valued_decomposition_smul_integers w) hπ hfix hx

/-- **The local Herbrand quotient `h(O_wˣ) = 1` at an unramified place.** -/
theorem herbrand_adicCompletionIntegers_units_eq_one
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : decompositionGroup K L w} (hσ : ∀ d : decompositionGroup K L w,
      d ∈ Subgroup.zpowers σ) :
    CyclicTate.herbrand (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ = 1 := by
  haveI := faithfulSMul_residueField_integers v w h
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer_integers v w h
  exact LocalCFT.herbrand_units_eq_one hσ (valued_decomposition_smul_integers w) hπ hfix

end Cohomology

end NumberField
