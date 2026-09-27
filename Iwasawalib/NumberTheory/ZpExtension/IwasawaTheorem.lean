/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.EventualClassNumberBridge
public import Iwasawalib.NumberTheory.ZpExtension.YnStability
public import Iwasawalib.NumberTheory.ZpExtension.FiniteSubalgebraLinearDisjoint
public import Iwasawalib.NumberTheory.ZpExtension.BaseChangeLinearDisjoint
public import Iwasawalib.NumberTheory.ZpExtension.Linf
public import Iwasawalib.NumberTheory.ZpExtension.TameLocalExponent
public import Iwasawalib.NumberTheory.ZpExtension.YnGenerators

@[expose] public section

/-!
# Iwasawa's theorem on the growth of class numbers in a `ℤₚ`-extension

Source: Washington, *Introduction to cyclotomic fields*, Theorem 13.13 (Iwasawa 1959,
Theorem 11); blueprint node `clgp-growth`.  Let `K∞ / K` be a `ℤₚ`-extension of a number field
with layers `Kₙ`.  Then there are integers `μ ≥ 0`, `λ ≥ 0` and `ν` such that
`ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all sufficiently large `n`.

This file proves, without `sorryAx`, the assembly step of that theorem; the theorem itself is
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`
(`Iwasawalib/NumberTheory/ZpExtension/IwasawaTheoremOfHCF.lean`), which supplies the cardinality
bridge below from the two Hilbert class field hypotheses of
`Iwasawalib/NumberTheory/NumberField/HilbertClassField/Hypothesis.lean`.

The assembly takes three inputs, each of which comes with its own threshold:

* the generator description `Y_n = ℤ_p·(ν_{n,e₁}·a) + ω_n X∞` for `n ≥ e₁` (the hypothesis
  `hgen` of `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_data`);
* the `Λ`-submodule `Y` with `ν_{n,e}·Y = Y_n` (the hypothesis `hYdata` of the same theorem),
  which is a consequence of the generator description at the same threshold;
* the cardinality bridge `#Gal(K∞ Lₙ / K∞) = p ^ ord_p(h_{Kₙ})` for `n ≥ e₂`
  (`MvZpExtension.EventualClassNumberCardinalityBridge`).

All three are moved to the common threshold `max e₁ e₂`.

## Main statements

* `MvZpExtension.reindex_eventual_Yn_generators`: the generator description may be restarted at
  a later threshold `e' ≥ e`, with some finite set `a'` (one may take `ν_{e',e}·a`).
* `MvZpExtension.exists_eventual_Yn_lambda_data_of_generators`: the generator description at
  threshold `e` produces a `Λ`-submodule `Y` with `Y = Y_e` and `ν_{n,e}·Y = Y_n` for `n ≥ e`.
* `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_generators`: Iwasawa's formula
  from the generator description at a threshold `e₁` and the cardinality bridge at a threshold
  `e₂`, with no relation assumed between `e₁` and `e₂`.
-/

open Module PowerSeries NumberField IsDedekindDomain
open scoped Pointwise

namespace MvZpExtension

section Threshold

variable {p : ℕ} [hp : Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf]
  [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

set_option synthInstance.maxHeartbeats 800000 in
/-- **The generator description of `Y_n` may be restarted at a later threshold.**  If
`Y_n = ℤ_p·(ν_{n,e}·a) + ω_n X∞` for all `n ≥ e` and `e ≤ e'`, then there is a finite set `a'`
with `Y_n = ℤ_p·(ν_{n,e'}·a') + ω_n X∞` for all `n ≥ e'`.  One may take `a' = ν_{e',e}·a`,
since `ν_{n,e'} ν_{e',e} = ν_{n,e}` (`MvZpExtension.nu_mul_nu`) and the summand `ω_n X∞` does
not involve the threshold.

This is the companion, for the hypothesis `hgen` of
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_data`, of
`MvZpExtension.reindex_eventual_Yn_lambda_data` and of
`MvZpExtension.EventualClassNumberCardinalityBridge.of_le`.

Proved without `sorryAx`. -/
theorem reindex_eventual_Yn_generators
    (γ : H.GG ⧸ H.Xinf) {e e' : ℕ} (hee' : e ≤ e')
    (a : Finset (Additive ↑H.Xinf))
    (hgen : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      ∀ n : ℕ, e ≤ n →
        H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n) =
          Submodule.span ℤ_[p]
              (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
                (a : Set (Additive ↑H.Xinf))) ⊔
            ((Ideal.span
                {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
                  ℤ_[p]⟦X⟧)} •
              (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↑H.Xinf))).restrictScalars ℤ_[p])) :
    letI := H.XinfZpModule
    letI := H.XinfLambdaModule γ
    haveI := H.isScalarTower_Xinf γ
    ∃ a' : Finset (Additive ↑H.Xinf),
      ∀ n : ℕ, e' ≤ n →
        H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n) =
          Submodule.span ℤ_[p]
              (((Polynomial.nu ℤ_[p] p n e' : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
                (a' : Set (Additive ↑H.Xinf))) ⊔
            ((Ideal.span
                {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
                  ℤ_[p]⟦X⟧)} •
              (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↑H.Xinf))).restrictScalars ℤ_[p]) := by
  classical
  letI := H.XinfZpModule
  letI := H.XinfLambdaModule γ
  haveI := H.isScalarTower_Xinf γ
  refine ⟨a.image fun x ↦
    ((Polynomial.nu ℤ_[p] p e' e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • x, fun n hn ↦ ?_⟩
  rw [Finset.coe_image, Set.image_smul, smul_smul, ← Polynomial.coe_mul, nu_mul_nu hee' hn]
  exact hgen n (hee'.trans hn)

set_option synthInstance.maxHeartbeats 800000 in
/-- **The `Λ`-submodule `Y` from the generator description.**  If
`Y_n = ℤ_p·(ν_{n,e}·a) + ω_n X∞` for all `n ≥ e`, then there is a `Λ`-submodule `Y` of
`Additive X∞` whose underlying `ℤ_p`-submodule is the one attached to `Y_e` and such that the
`ℤ_p`-submodule underlying `ν_{n,e}·Y` is the one attached to `Y_n`, for every `n ≥ e`.

The submodule is `MvZpExtension.YnStableSubmodule γ e`
(`MvZpExtension.YnStableSubmodule_restrictScalars`); the second property is
`MvZpExtension.hstep2_of_generators` read through
`IwasawaAlgebra.map_lsmulZp_restrictScalars_smul`.

The conclusion is exactly the hypothesis `hYdata` of
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_data`, at the same `γ` and `e`.

Proved without `sorryAx`. -/
theorem exists_eventual_Yn_lambda_data_of_generators
    (γ : H.GG ⧸ H.Xinf) (e : ℕ) (a : Finset (Additive ↑H.Xinf))
    (hgen : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      ∀ n : ℕ, e ≤ n →
        H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n) =
          Submodule.span ℤ_[p]
              (((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
                (a : Set (Additive ↑H.Xinf))) ⊔
            ((Ideal.span
                {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
                  ℤ_[p]⟦X⟧)} •
              (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↑H.Xinf))).restrictScalars ℤ_[p])) :
    letI := H.XinfZpModule
    letI := H.XinfLambdaModule γ
    haveI := H.isScalarTower_Xinf γ
    ∃ Y : Submodule ℤ_[p]⟦X⟧ (Additive ↑H.Xinf),
      Y.restrictScalars ℤ_[p] =
          H.xinfZpSubmoduleOfSubgroup (H.YnIn e) (H.isClosed_YnIn e) ∧
        ∀ n : ℕ, e ≤ n →
          (((((Polynomial.nu ℤ_[p] p n e : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) • Y).restrictScalars
              ℤ_[p])) =
            H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n) := by
  letI := H.XinfZpModule
  letI := H.XinfLambdaModule γ
  haveI := H.isScalarTower_Xinf γ
  refine ⟨H.YnStableSubmodule γ e, H.YnStableSubmodule_restrictScalars γ e, fun n hn ↦ ?_⟩
  rw [← IwasawaAlgebra.map_lsmulZp_restrictScalars_smul, H.YnStableSubmodule_restrictScalars γ e]
  exact H.hstep2_of_generators γ e a hgen n hn

set_option synthInstance.maxHeartbeats 800000 in
/-- **Iwasawa's class-number formula from the generator description and the cardinality
bridge, at independent thresholds.**  Let `γ` be a topological generator of `G ⧸ X∞`.  If
`Y_n = ℤ_p·(ν_{n,e₁}·a) + ω_n X∞` for all `n ≥ e₁`, and
`#Gal(K∞ Lₙ / K∞) = p ^ ord_p(h_{Kₙ})` for all `n ≥ e₂`, then
`ord_p(h_{Kₙ}) = μ pⁿ + λ n + ν` for all sufficiently large `n`.

This is `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_data` at the threshold
`max e₁ e₂`: the generator description is moved there by
`MvZpExtension.reindex_eventual_Yn_generators`, the bridge by
`MvZpExtension.EventualClassNumberCardinalityBridge.of_le`, and the hypothesis `hYdata` is
`MvZpExtension.exists_eventual_Yn_lambda_data_of_generators`.

Proved without `sorryAx`.  In `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_hcf`, `hgen` is
supplied by `MvZpExtension.exists_eventual_Yn_generators` and `hbridge` by
`MvZpExtension.exists_eventualClassNumberCardinalityBridge_of_hcf`. -/
theorem multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_generators
    [Unique ι]
    (γ : H.GG ⧸ H.Xinf)
    (hγ : Dense (Subgroup.zpowers γ : Set (H.GG ⧸ H.Xinf)))
    {e₁ e₂ : ℕ} (a : Finset (Additive ↑H.Xinf))
    (hgen : letI := H.XinfZpModule
      letI := H.XinfLambdaModule γ
      haveI := H.isScalarTower_Xinf γ
      ∀ n : ℕ, e₁ ≤ n →
        H.xinfZpSubmoduleOfSubgroup (H.YnIn n) (H.isClosed_YnIn n) =
          Submodule.span ℤ_[p]
              (((Polynomial.nu ℤ_[p] p n e₁ : Polynomial ℤ_[p]) : ℤ_[p]⟦X⟧) •
                (a : Set (Additive ↑H.Xinf))) ⊔
            ((Ideal.span
                {((Polynomial.oneAddXPowSubOne ℤ_[p] (p ^ n) : Polynomial ℤ_[p]) :
                  ℤ_[p]⟦X⟧)} •
              (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive ↑H.Xinf))).restrictScalars ℤ_[p]))
    (hbridge : EventualClassNumberCardinalityBridge H e₂) :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      (multiplicity p (NumberField.classNumber (H.Kn n)) : ℤ) =
        (mu : ℤ) * (p : ℤ) ^ n + (lambda : ℤ) * n + nu := by
  obtain ⟨a', hgen'⟩ :=
    H.reindex_eventual_Yn_generators γ (le_max_left e₁ e₂) a hgen
  exact H.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_data γ hγ (max e₁ e₂) a' hgen'
    (H.exists_eventual_Yn_lambda_data_of_generators γ (max e₁ e₂) a' hgen')
    (EventualClassNumberCardinalityBridge.of_le H hbridge (le_max_right e₁ e₂))

end Threshold

end MvZpExtension
