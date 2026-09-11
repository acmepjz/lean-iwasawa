/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.GaloisGroupProP
public import Iwasawalib.RingTheory.IwasawaAlgebra.ProPGammaModule

@[expose] public section

/-!
# `X∞` is a `Λ`-module — blueprint node `X-has-Gamma-action`, completed

Let `K∞ / K` be a `ℤₚᵈ`-extension of number fields, `L∞` the union of the maximal unramified
abelian `p`-extensions of the layers, `G = Gal(L∞/K)` and `X∞ = Gal(L∞/K∞) ⊆ G`.  The
exact sequence `1 → X∞ → G → Γ → 1` and the conjugation action of `Γ = G ⧸ X∞` on `X∞` were
built in `Iwasawalib.NumberTheory.ZpExtension.Linf`
(`MvZpExtension.XinfConjQuotient`, `MvZpExtension.continuous_XinfConjQuotient`).  This file
supplies the coefficients and completes the node:

* `X∞` is a *closed* subgroup of the profinite group `G` (`MvZpExtension.isClosed_Xinf`),
  hence profinite, and it is commutative (`MvZpExtension.mul_comm_Xinf`);
* `G` is pro-`p` (`MvZpExtension.isProP_GG`), hence so are `X∞` and `Γ`;
* therefore `Additive X∞` is a `ℤ_p`-module (`ProP.additivePadicModule`), the `Γ`-action is
  `ℤ_p`-linear for free (`ProP.map_padicSMul`), and `Γ` contains elements `γ` with
  `γ ^ (p ^ n) → 1` (`IsProP.tendsto_pow`);
* so `IwasawaAlgebra.gammaLambdaModule` applies, through `ProP.gammaLambdaModule`.

The uniform structure used throughout is `IsTopologicalGroup.rightUniformSpace`, which on a
commutative topological group induces the given topology; it appears in no statement.

## Main definitions

* `MvZpExtension.XinfZpModule`: `Additive X∞` is a `ℤ_p`-module.
* `MvZpExtension.XinfLambdaModule`: given `γ : Γ`, `Additive X∞` is a `Λ = ℤ_p⟦X⟧`-module with
  `X` acting as `γ - 1`.

## Main results

* `MvZpExtension.continuousSMul_XinfLambdaModule`: the `Λ`-action is continuous.
* `MvZpExtension.XinfLambdaModule_X_smul`: `X • x = γ x γ⁻¹ · x⁻¹`.
* `MvZpExtension.eq_XinfLambdaModule_smul`: the structure is unique.
-/

open Topology Filter PowerSeries
open scoped PowerSeries.WithPiTopology

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- The uniform structure on `X∞` used to build its `ℤ_p`- and `Λ`-module structures: the
canonical right uniformity of the topological group `X∞`, which induces its topology.  It
occurs in no statement of this file. -/
noncomputable abbrev XinfUniformSpace : UniformSpace ↥H.Xinf :=
  IsTopologicalGroup.rightUniformSpace _

/-- **Blueprint node `X-has-Gamma-action`, coefficients.**  `Additive X∞` is a `ℤ_p`-module:
`X∞` is a profinite abelian pro-`p` group. -/
@[instance_reducible] noncomputable def XinfZpModule : Module ℤ_[p] (Additive ↥H.Xinf) :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.additivePadicModule H.isProP_Xinf'

/-- The `ℤ_p`-action on `Additive X∞` is continuous. -/
theorem continuousSMul_XinfZpModule :
    letI := H.XinfZpModule
    ContinuousSMul ℤ_[p] (Additive ↥H.Xinf) :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.continuousSMul_additivePadicModule H.isProP_Xinf'

/-- **What the `ℤ_p`-scalars do**: `a • x` is the limit of the integer powers `x ^ (a.appr n)`. -/
theorem tendsto_zpow_appr_XinfZpModule (a : ℤ_[p]) (x : ↥H.Xinf) :
    letI := H.XinfZpModule
    Tendsto (fun n : ℕ ↦ Additive.ofMul (x ^ ((a.appr n : ℤ)))) atTop
      (𝓝 (a • Additive.ofMul x)) :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.tendsto_zpow_appr H.isProP_Xinf' a x

/-- **Blueprint node `X-has-Gamma-action`.**  For any `γ : Γ = G ⧸ X∞`, the group `X∞` is a
`Λ = ℤ_p⟦X⟧`-module in which `X` acts by `x ↦ γ x γ⁻¹ · x⁻¹`. -/
@[instance_reducible] noncomputable def XinfLambdaModule (γ : H.GG ⧸ H.Xinf) :
    Module ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.gammaLambdaModule H.isProP_Xinf' H.XinfConjQuotient H.continuous_XinfConjQuotient γ
    (H.tendsto_pow_gammaQuotient γ)

/-- The `Λ`-module structure on `X∞` is continuous. -/
theorem continuousSMul_XinfLambdaModule (γ : H.GG ⧸ H.Xinf) :
    letI := H.XinfLambdaModule γ
    ContinuousSMul ℤ_[p]⟦X⟧ (Additive ↥H.Xinf) :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.continuousSMul_gammaLambdaModule H.isProP_Xinf' H.XinfConjQuotient
    H.continuous_XinfConjQuotient γ (H.tendsto_pow_gammaQuotient γ)

/-- **`X = T` acts as `γ - 1`**: in multiplicative notation, `x ↦ (γ x γ⁻¹) / x`. -/
theorem XinfLambdaModule_X_smul (γ : H.GG ⧸ H.Xinf) (x : ↥H.Xinf) :
    letI := H.XinfLambdaModule γ
    (X : ℤ_[p]⟦X⟧) • (Additive.ofMul x)
      = Additive.ofMul ((H.XinfConjQuotient γ x : ↥H.Xinf) / x) :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.gammaLambdaModule_X_smul H.isProP_Xinf' H.XinfConjQuotient
    H.continuous_XinfConjQuotient γ (H.tendsto_pow_gammaQuotient γ) x

/-- The `ℤ_p` ⊆ `Λ` scalars act by `MvZpExtension.XinfZpModule`. -/
theorem XinfLambdaModule_C_smul (γ : H.GG ⧸ H.Xinf) (a : ℤ_[p]) (x : Additive ↥H.Xinf) :
    letI := H.XinfZpModule
    letI := H.XinfLambdaModule γ
    (PowerSeries.C a : ℤ_[p]⟦X⟧) • x = a • x :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.gammaLambdaModule_C_smul H.isProP_Xinf' H.XinfConjQuotient
    H.continuous_XinfConjQuotient γ (H.tendsto_pow_gammaQuotient γ) a x

/-- **Uniqueness of the `Λ`-module structure on `X∞`.** -/
theorem eq_XinfLambdaModule_smul (γ : H.GG ⧸ H.Xinf)
    {σ : ℤ_[p]⟦X⟧ → Additive ↥H.Xinf → Additive ↥H.Xinf}
    (hadd : ∀ a b z, σ (a + b) z = σ a z + σ b z)
    (hmul : ∀ a b z, σ (a * b) z = σ a (σ b z))
    (hone : ∀ z, σ 1 z = z)
    (hzp : letI := H.XinfZpModule
      ∀ (a : ℤ_[p]) (b : ℤ_[p]⟦X⟧) (z : Additive ↥H.Xinf), σ (a • b) z = a • σ b z)
    (hcont : ∀ z, Continuous fun a ↦ σ a z)
    (hX : ∀ x : ↥H.Xinf, σ (X : ℤ_[p]⟦X⟧) (Additive.ofMul x)
      = Additive.ofMul ((H.XinfConjQuotient γ x : ↥H.Xinf) / x))
    (a : ℤ_[p]⟦X⟧) (x : Additive ↥H.Xinf) :
    letI := H.XinfLambdaModule γ
    σ a x = a • x :=
  letI := H.XinfUniformSpace
  haveI : IsUniformGroup ↥H.Xinf := isUniformGroup_of_commGroup
  ProP.eq_gammaLambdaModule_smul H.isProP_Xinf' H.XinfConjQuotient
    H.continuous_XinfConjQuotient γ (H.tendsto_pow_gammaQuotient γ) hadd hmul hone hzp hcont hX a x

end MvZpExtension
