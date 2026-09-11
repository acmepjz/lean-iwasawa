/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.Linf
public import Iwasawalib.NumberTheory.ZpExtension.ProPGalois
public import Iwasawalib.RingTheory.IwasawaAlgebra.ProPModule
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section

/-!
# `X∞ = Gal(L∞/K∞)` is a continuous `ℤ_p`-module

The group-theoretic half of blueprint node `X-has-Gamma-action` was already available
(`MvZpExtension.Xinf`, `MvZpExtension.XinfConjQuotient`,
`MvZpExtension.continuous_XinfConjQuotient`).  What was missing was the coefficient ring: the
`Λ`-module machinery of `Iwasawalib.RingTheory.IwasawaAlgebra.GammaModule` runs on an
*additive* profinite `ℤ_p`-module, while `X∞` is a multiplicative profinite abelian pro-`p`
group.  This file supplies the bridge, by combining

* `isProP_galoisGroup`: the Galois group of a `{p}`-extension is pro-`p`;
* `ProP.additivePadicModule`: a profinite abelian pro-`p` group is a `ℤ_p`-module.

The uniform structure used inside the proofs is `IsTopologicalGroup.rightUniformSpace`, which
on a commutative topological group is a `IsUniformGroup` structure inducing the given
topology; it does not appear in any statement.

## Main results

* `galoisGroupPadicModule`: `Additive Gal(L/F)` is a `ℤ_p`-module for an abelian
  `{p}`-extension `L/F`.
* `continuousSMul_galoisGroupPadicModule`: the action is continuous.
* `MvZpExtension.XinfPadicModule`: the case `L∞ / K∞`, i.e. `X∞`.
-/

open Filter Topology
open scoped IsMulCommutative

section General

variable (p : ℕ) [Fact p.Prime] (F L : Type*) [Field F] [Field L] [Algebra F L]
  [IsAbelianGalois F L] [IsSExtension F L {p}]

/-- **The `ℤ_p`-module bridge for Galois groups.**  If `L / F` is an abelian extension all of
whose finite subextensions have `p`-power degree, then `Gal(L/F)` — a profinite abelian
pro-`p` group — makes `Additive Gal(L/F)` a `ℤ_p`-module.  The scalar multiplication is
described by `tendsto_zpow_appr_galoisGroup`. -/
@[instance_reducible] noncomputable def galoisGroupPadicModule :
    Module ℤ_[p] (Additive Gal(L/F)) :=
  letI : UniformSpace Gal(L/F) := IsTopologicalGroup.rightUniformSpace _
  haveI : IsUniformGroup Gal(L/F) := isUniformGroup_of_commGroup
  ProP.additivePadicModule (isProP_galoisGroup p F L)

/-- The `ℤ_p`-action on `Additive Gal(L/F)` is continuous. -/
theorem continuousSMul_galoisGroupPadicModule :
    letI := galoisGroupPadicModule p F L
    ContinuousSMul ℤ_[p] (Additive Gal(L/F)) :=
  letI : UniformSpace Gal(L/F) := IsTopologicalGroup.rightUniformSpace _
  haveI : IsUniformGroup Gal(L/F) := isUniformGroup_of_commGroup
  ProP.continuousSMul_additivePadicModule (isProP_galoisGroup p F L)

variable {p F L}

/-- **What the scalars do**: `a • σ` is the limit of the integer powers `σ ^ (a.appr n)`. -/
theorem tendsto_zpow_appr_galoisGroup (a : ℤ_[p]) (σ : Gal(L/F)) :
    letI := galoisGroupPadicModule p F L
    Tendsto (fun n : ℕ ↦ Additive.ofMul (σ ^ ((a.appr n : ℤ)))) atTop
      (𝓝 (a • Additive.ofMul σ)) :=
  letI : UniformSpace Gal(L/F) := IsTopologicalGroup.rightUniformSpace _
  haveI : IsUniformGroup Gal(L/F) := isUniformGroup_of_commGroup
  ProP.tendsto_zpow_appr (isProP_galoisGroup p F L) a σ

/-- Integer scalars act as integer powers. -/
theorem galoisGroupPadicModule_intCast_smul (k : ℤ) (σ : Gal(L/F)) :
    letI := galoisGroupPadicModule p F L
    ((k : ℤ_[p])) • Additive.ofMul σ = Additive.ofMul (σ ^ k) :=
  letI : UniformSpace Gal(L/F) := IsTopologicalGroup.rightUniformSpace _
  haveI : IsUniformGroup Gal(L/F) := isUniformGroup_of_commGroup
  ProP.padicSMul_intCast (A := Additive Gal(L/F)) (isProP_galoisGroup p F L) k
    (Additive.ofMul σ)

end General

namespace MvZpExtension

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]
variable (H : MvZpExtension p ι K Kinf)

/-- **Blueprint node `X-has-Gamma-action`, coefficient half.**  `X∞ = Gal(L∞/K∞)` is a
profinite abelian pro-`p` group, hence `Additive X∞` is a `ℤ_p`-module.  Together with
`MvZpExtension.XinfConjQuotient` and
`IwasawaAlgebra.gammaLambdaModule` this is the `Λ`-module structure on `X∞`. -/
@[instance_reducible] noncomputable def XinfPadicModule :
    Module ℤ_[p] (Additive Gal(↥H.Linf/Kinf)) :=
  galoisGroupPadicModule p Kinf ↥H.Linf

/-- The `ℤ_p`-action on `X∞` is continuous. -/
theorem continuousSMul_XinfPadicModule :
    letI := H.XinfPadicModule
    ContinuousSMul ℤ_[p] (Additive Gal(↥H.Linf/Kinf)) :=
  continuousSMul_galoisGroupPadicModule p Kinf ↥H.Linf

/-- `X∞ = Gal(L∞/K∞)` is pro-`p`. -/
theorem isProP_Xinf : IsProP p Gal(↥H.Linf/Kinf) :=
  isProP_galoisGroup p Kinf ↥H.Linf

end MvZpExtension
