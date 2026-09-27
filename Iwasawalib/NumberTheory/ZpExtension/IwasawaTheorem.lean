/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.EventualClassNumberBridge
public import Iwasawalib.NumberTheory.ZpExtension.YnStability
public import Iwasawalib.NumberTheory.ZpExtension.EventualClassNumberBridgeOfCFT
public import Iwasawalib.NumberTheory.ZpExtension.TameLocalExponent
public import Iwasawalib.NumberTheory.ZpExtension.YnGenerators

@[expose] public section

/-!
# Iwasawa's theorem on the growth of class numbers in a `ℤₚ`-extension

Source: Washington, *Introduction to cyclotomic fields*, Theorem 13.13 (Iwasawa 1959,
Theorem 11); blueprint node `clgp-growth`.  Let `K∞ / K` be a `ℤₚ`-extension of a number field
with layers `Kₙ`.  Then there are integers `μ ≥ 0`, `λ ≥ 0` and `ν` such that
`ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all sufficiently large `n`.

**The final theorem of this file, `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_cft`, is
conditional**: its proof depends on `sorryAx` through the class field theory `sorry`s of
`Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory`.  The `sorry` of
`MvZpExtension.multiplicity_classNumber_Kn_eq₁` in
`Iwasawalib/NumberTheory/ZpExtension/ClassGroup.lean` is intentionally left in place.  The
other three theorems of this file are proved without `sorryAx`.

The file assembles the theorem from three inputs, each of which comes with its own threshold:

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
* `MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_cft`: **Iwasawa's theorem**, with the
  statement of `MvZpExtension.multiplicity_classNumber_Kn_eq₁`.  **Conditional on class field
  theory**, see its docstring.
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

Proved without `sorryAx`: the class field theory is in the two hypotheses. -/
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

section Main

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*}
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

variable (H : MvZpExtension p ι K Kinf)

/-- **Iwasawa's theorem** on growth of class groups of `ℤₚ`-extension of number fields
(Washington, Theorem 13.13): for a `ℤₚ`-extension `K∞ / K` of a number field with layers `Kₙ`
there are natural numbers `μ`, `λ`, an integer `ν` and a bound `N` such that
`ord_p #Cl(Kₙ) = μ pⁿ + λ n + ν` for all `n > N`.

The statement is that of `MvZpExtension.multiplicity_classNumber_Kn_eq₁`.

**Warning**: this declaration is *not* unconditional.  It has no hypothesis named "cft": the
suffix records that its proof depends on `sorryAx` through the class field theory `sorry`s of
`Iwasawalib.NumberTheory.NumberField.HilbertClassField.ClassFieldTheory`, by two routes.

* Through `MvZpExtension.exists_eventualClassNumberCardinalityBridge`, which uses
  `MvZpExtension.finrank_Ln` (derived from
  `NumberField.IsUnramifiedEverywhere.bijective_artinMap_of_isSepClosed`), the instance
  `MvZpExtension.finiteDimensional_Ln` and `MvZpExtension.exists_inertiaSubgroup_ne_bot` (both
  derived from `NumberField.IsUnramifiedEverywhere.surjective_artinMap`).
* Through `MvZpExtension.exists_eventual_Yn_generators` (YnGenerators.lean), that is
  `MvZpExtension.RamifiedBasePlaceData.exists_eventual_Yn_generators` (YnGenerators.lean), which
  needs a ramified place and obtains it from `MvZpExtension.exists_inertiaSubgroup_ne_bot`
  via `MvZpExtension.RamifiedBasePlaceData.nonempty_orbitIndex`, hence from
  `NumberField.IsUnramifiedEverywhere.surjective_artinMap`.

`NumberField.IsUnramifiedEverywhere.surjective_artinMap` and
`NumberField.IsUnramifiedEverywhere.bijective_artinMap_of_isSepClosed` are `sorry`, and
`NumberField.IsUnramifiedEverywhere.artinMap` is itself defined by `sorry`.
The local input at the primes not above `p`,
`MvZpExtension.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv`, and the assembly
`MvZpExtension.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_generators` do not depend on
`sorryAx`.

The `sorry` of `MvZpExtension.multiplicity_classNumber_Kn_eq₁` in
`Iwasawalib/NumberTheory/ZpExtension/ClassGroup.lean` is intentionally left in place: that
declaration is the statement of the theorem, and it is not replaced by a proof which depends
on `sorryAx`. -/
theorem multiplicity_classNumber_Kn_eq₁_of_cft [Unique ι] :
    ∃ (mu lambda : ℕ) (nu : ℤ) (N : ℕ), ∀ n > N,
      multiplicity p (NumberField.classNumber (H.Kn n)) = mu * p ^ n + lambda * n + nu := by
  obtain ⟨γ, hγ, e₁, a, hgen⟩ := H.exists_eventual_Yn_generators
    H.exists_restrictNormalHom_pow_eq_one_of_liesOver_adicAbv
  obtain ⟨e₂, hbridge⟩ := H.exists_eventualClassNumberCardinalityBridge
  exact H.multiplicity_classNumber_Kn_eq₁_of_eventual_Yn_generators γ hγ a hgen hbridge

end Main

end MvZpExtension
