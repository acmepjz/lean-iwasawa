/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.ProPModule
public import Iwasawalib.RingTheory.IwasawaAlgebra.GammaModule

@[expose] public section

/-!
# A profinite abelian pro-`p` group with a continuous `Γ`-action is a `Λ`-module

This file joins the two halves that
`Iwasawalib.RingTheory.IwasawaAlgebra.ProPModule` and
`Iwasawalib.RingTheory.IwasawaAlgebra.GammaModule` leave apart.

Let `G` be a profinite abelian group written *multiplicatively*, which is pro-`p`, and let a
topological group `Γ` act on it continuously by group automorphisms, i.e. through a
homomorphism `f : Γ →* MulAut G` whose uncurried action is continuous.  Let `γ : Γ` satisfy
`γ ^ (p ^ n) → 1`.  Then `Additive G` is a `Λ = ℤ_p⟦X⟧`-module with `X` acting as `γ - 1`,
and that structure is unique.

The three ingredients that had to be supplied here are:

* `ProP.additiveMulAut`: turning `f : Γ →* MulAut G` into `DistribMulAction Γ (Additive G)`
  (Mathlib has `MulDistribMulAction` and the type synonym `Additive`, but no transfer between
  them);
* the `SMulCommClass Γ ℤ_[p] (Additive G)` hypothesis of
  `IwasawaAlgebra.gammaLambdaModule`, which is *automatic* here: every continuous additive
  endomorphism of a profinite pro-`p` group is `ℤ_p`-linear (`ProP.map_padicSMul`);
* the uniform structure.  `IwasawaAlgebra.gammaLambdaModule` runs on a uniform additive group;
  a commutative topological group has the canonical `IsTopologicalGroup.rightUniformSpace`,
  which induces the given topology, so this is a `letI` that never escapes into a statement.

## Main definitions

* `ProP.additiveMulAut`, `ProP.continuousSMul_additiveMulAut`: the `Γ`-action on `Additive G`.
* `ProP.gammaLambdaModule`: the `Λ`-module structure.
* `ProP.continuousSMul_gammaLambdaModule`, `ProP.gammaLambdaModule_X_smul`,
  `ProP.gammaLambdaModule_C_smul`, `ProP.eq_gammaLambdaModule_smul`: it is continuous, `X`
  acts as `γ - 1`, `ℤ_p` acts as before, and it is the unique such structure.
-/

open Topology Filter PowerSeries
open scoped PowerSeries.WithPiTopology

namespace ProP

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [CommGroup G]
variable {Γ : Type*} [Group Γ]

/-! ### From `Γ →* MulAut G` to a `DistribMulAction` on `Additive G` -/

section Action

variable [TopologicalSpace G] [TopologicalSpace Γ]

/-- An action of `Γ` on a commutative group `G` by group automorphisms is a distributive
action on `Additive G`. -/
@[instance_reducible] def additiveMulAut (f : Γ →* MulAut G) :
    DistribMulAction Γ (Additive G) where
  smul σ x := Additive.ofMul (f σ (Additive.toMul x))
  one_smul x := by
    show Additive.ofMul (f 1 (Additive.toMul x)) = x
    rw [map_one]; rfl
  mul_smul σ τ x := by
    show Additive.ofMul (f (σ * τ) (Additive.toMul x))
      = Additive.ofMul (f σ (Additive.toMul (Additive.ofMul (f τ (Additive.toMul x)))))
    rw [map_mul]; rfl
  smul_zero σ := by
    show Additive.ofMul (f σ (1 : G)) = Additive.ofMul (1 : G)
    rw [map_one]
  smul_add σ x y := by
    show Additive.ofMul (f σ (Additive.toMul x * Additive.toMul y))
      = Additive.ofMul (f σ (Additive.toMul x)) + Additive.ofMul (f σ (Additive.toMul y))
    rw [map_mul]; rfl

omit [TopologicalSpace G] [TopologicalSpace Γ] in
theorem additiveMulAut_smul (f : Γ →* MulAut G) (σ : Γ) (x : Additive G) :
    letI := additiveMulAut f
    σ • x = Additive.ofMul (f σ (Additive.toMul x)) := rfl

/-- The action of `ProP.additiveMulAut` is continuous when the action on `G` is. -/
theorem continuousSMul_additiveMulAut (f : Γ →* MulAut G)
    (hf : Continuous fun q : Γ × G ↦ (f q.1 q.2 : G)) :
    letI := additiveMulAut f
    ContinuousSMul Γ (Additive G) :=
  letI := additiveMulAut f
  ⟨hf⟩

/-- `σ : Γ` acts on `Additive G` by a continuous additive endomorphism. -/
def additiveMulAutHom (f : Γ →* MulAut G) (σ : Γ) : Additive G →+ Additive G where
  toFun x := Additive.ofMul (f σ (Additive.toMul x))
  map_zero' := by
    show Additive.ofMul (f σ (1 : G)) = Additive.ofMul (1 : G)
    rw [map_one]
  map_add' x y := by
    show Additive.ofMul (f σ (Additive.toMul x * Additive.toMul y))
      = Additive.ofMul (f σ (Additive.toMul x)) + Additive.ofMul (f σ (Additive.toMul y))
    rw [map_mul]; rfl

omit [TopologicalSpace G] [TopologicalSpace Γ] in
/-- In additive notation, `γ • x - x` is `g ↦ (f γ g) / g`. -/
theorem additiveMulAut_smul_sub (f : Γ →* MulAut G) (γ : Γ) (g : G) :
    letI := additiveMulAut f
    γ • (Additive.ofMul g) - Additive.ofMul g = Additive.ofMul ((f γ g : G) / g) := rfl

theorem continuous_additiveMulAutHom (f : Γ →* MulAut G)
    (hf : Continuous fun q : Γ × G ↦ (f q.1 q.2 : G)) (σ : Γ) :
    Continuous (additiveMulAutHom f σ) :=
  hf.comp (continuous_const.prodMk continuous_id)

end Action

/-! ### The `Λ`-module structure -/

section Lambda

variable [UniformSpace G] [IsUniformGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [TopologicalSpace Γ]

variable (hG : IsProP p G) (f : Γ →* MulAut G)
  (hf : Continuous fun q : Γ × G ↦ (f q.1 q.2 : G))

include hG hf

/-- The `Γ`-action on `Additive G` commutes with the `ℤ_p`-action of
`ProP.additivePadicModule`.  This is automatic: `ProP.map_padicSMul` says every continuous
additive endomorphism is `ℤ_p`-linear. -/
theorem smulCommClass_additiveMulAut :
    letI := additivePadicModule hG
    letI := additiveMulAut f
    SMulCommClass Γ ℤ_[p] (Additive G) :=
  letI := additivePadicModule hG
  letI := additiveMulAut f
  ⟨fun σ a x ↦ map_padicSMul (A := Additive G) hG
    (f := additiveMulAutHom f σ) (continuous_additiveMulAutHom f hf σ) a x⟩

variable (γ : Γ) (hγ : Tendsto (fun n : ℕ ↦ γ ^ p ^ n) atTop (𝓝 1))

include hγ

/-- **The `Λ`-module structure on a profinite abelian pro-`p` group with a continuous
`Γ`-action.**  `X` acts as `γ - 1`; see `ProP.gammaLambdaModule_X_smul`. -/
@[instance_reducible] noncomputable def gammaLambdaModule : Module ℤ_[p]⟦X⟧ (Additive G) :=
  letI := additivePadicModule hG
  haveI := continuousSMul_additivePadicModule hG
  letI := additiveMulAut f
  haveI := continuousSMul_additiveMulAut f hf
  haveI := smulCommClass_additiveMulAut hG f hf
  IwasawaAlgebra.gammaLambdaModule (Z := Additive G) γ hγ

/-- The `Λ`-module structure of `ProP.gammaLambdaModule` is continuous. -/
theorem continuousSMul_gammaLambdaModule :
    letI := gammaLambdaModule hG f hf γ hγ
    ContinuousSMul ℤ_[p]⟦X⟧ (Additive G) :=
  letI := additivePadicModule hG
  haveI := continuousSMul_additivePadicModule hG
  letI := additiveMulAut f
  haveI := continuousSMul_additiveMulAut f hf
  haveI := smulCommClass_additiveMulAut hG f hf
  IwasawaAlgebra.continuousSMul_gammaLambdaModule (Z := Additive G) γ hγ

/-- **`X = T` acts as `γ - 1`**, i.e. as `g ↦ (f γ g) · g⁻¹` in multiplicative notation. -/
theorem gammaLambdaModule_X_smul (g : G) :
    letI := gammaLambdaModule hG f hf γ hγ
    (X : ℤ_[p]⟦X⟧) • (Additive.ofMul g) = Additive.ofMul ((f γ g : G) / g) :=
  letI := additivePadicModule hG
  haveI := continuousSMul_additivePadicModule hG
  letI := additiveMulAut f
  haveI := continuousSMul_additiveMulAut f hf
  haveI := smulCommClass_additiveMulAut hG f hf
  (IwasawaAlgebra.gammaLambdaModule_X_smul (Z := Additive G) γ hγ (Additive.ofMul g)).trans
    (additiveMulAut_smul_sub f γ g)

/-- The `ℤ_p`-scalars act through `ProP.padicSMul`, as before. -/
theorem gammaLambdaModule_C_smul (a : ℤ_[p]) (x : Additive G) :
    letI := gammaLambdaModule hG f hf γ hγ
    (PowerSeries.C a : ℤ_[p]⟦X⟧) • x = padicSMul a x :=
  letI := additivePadicModule hG
  haveI := continuousSMul_additivePadicModule hG
  letI := additiveMulAut f
  haveI := continuousSMul_additiveMulAut f hf
  haveI := smulCommClass_additiveMulAut hG f hf
  IwasawaAlgebra.gammaLambdaModule_C_smul (Z := Additive G) γ hγ a x

/-- **Uniqueness.**  Any `Λ`-action which is additive, multiplicative, unital, `ℤ_p`-semilinear,
continuous in the scalar, and sends `X` to `γ - 1`, is `ProP.gammaLambdaModule`. -/
theorem eq_gammaLambdaModule_smul
    {σ : ℤ_[p]⟦X⟧ → Additive G → Additive G}
    (hadd : ∀ a b z, σ (a + b) z = σ a z + σ b z)
    (hmul : ∀ a b z, σ (a * b) z = σ a (σ b z))
    (hone : ∀ z, σ 1 z = z)
    (hzp : ∀ (a : ℤ_[p]) (b : ℤ_[p]⟦X⟧) (z : Additive G), σ (a • b) z = padicSMul a (σ b z))
    (hcont : ∀ z, Continuous fun a ↦ σ a z)
    (hX : ∀ g : G, σ (X : ℤ_[p]⟦X⟧) (Additive.ofMul g) = Additive.ofMul ((f γ g : G) / g))
    (a : ℤ_[p]⟦X⟧) (x : Additive G) :
    letI := gammaLambdaModule hG f hf γ hγ
    σ a x = a • x :=
  letI := additivePadicModule hG
  haveI := continuousSMul_additivePadicModule hG
  letI := additiveMulAut f
  haveI := continuousSMul_additiveMulAut f hf
  haveI := smulCommClass_additiveMulAut hG f hf
  IwasawaAlgebra.eq_gammaLambdaModule_smul (Z := Additive G) γ hγ hadd hmul hone hzp hcont
    (fun z ↦ (hX (Additive.toMul z)).trans
      (additiveMulAut_smul_sub f γ (Additive.toMul z)).symm) a x

end Lambda

end ProP
