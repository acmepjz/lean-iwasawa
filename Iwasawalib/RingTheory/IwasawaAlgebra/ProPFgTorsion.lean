/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsionSpan
public import Iwasawalib.RingTheory.IwasawaAlgebra.ProPGammaModule

@[expose] public section

/-!
# The two facts about `ProP.gammaLambdaModule` that Step 3 needs

`Iwasawalib.RingTheory.IwasawaAlgebra.ProPGammaModule` builds the `Λ`-module structure on
`Additive G` for a profinite abelian pro-`p` group `G` with a continuous `Γ`-action, and
records how `X` and `ℤ_p` act.  Step 3 of blueprint node
`Xn-isom-qout-of-totally-ramified` needs two more things about that structure, both of which
are transports of facts already proved for `IwasawaAlgebra.gammaLambdaModule`:

* it extends the `ℤ_p`-structure `ProP.additivePadicModule`, as an `IsScalarTower` — every
  statement in `Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsion` and
  `Iwasawalib.RingTheory.IwasawaAlgebra.FgTorsionSpan` is stated over that tower;
* the submodule `T · Additive G = (X) · Additive G` has, as a *set*, the description
  `{(f γ g) / g | g ∈ G}` in multiplicative notation — which is the subgroup `T G` of blueprint
  node `commutator-eq`.

## Main results

* `ProP.isScalarTower_gammaLambdaModule`
* `ProP.coe_span_X_smul_top_additive`
-/

open Topology Filter PowerSeries
open scoped Pointwise
open scoped PowerSeries.WithPiTopology

namespace ProP

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [CommGroup G]
variable {Γ : Type*} [Group Γ]

section

variable [UniformSpace G] [IsUniformGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [TopologicalSpace Γ]

variable (hG : IsProP p G) (f : Γ →* MulAut G)
  (hf : Continuous fun q : Γ × G ↦ (f q.1 q.2 : G))
  (γ : Γ) (hγ : Tendsto (fun n : ℕ ↦ γ ^ p ^ n) atTop (𝓝 1))

include hG hf hγ

/-- **`ProP.gammaLambdaModule` extends `ProP.additivePadicModule`.** -/
theorem isScalarTower_gammaLambdaModule :
    letI := additivePadicModule hG
    letI := gammaLambdaModule hG f hf γ hγ
    IsScalarTower ℤ_[p] ℤ_[p]⟦X⟧ (Additive G) :=
  letI := additivePadicModule hG
  haveI := continuousSMul_additivePadicModule hG
  letI := additiveMulAut f
  haveI := continuousSMul_additiveMulAut f hf
  haveI := smulCommClass_additiveMulAut hG f hf
  IwasawaAlgebra.isScalarTower_gammaLambdaModule (Z := Additive G) γ hγ

/-- **`T · Additive G` is the subgroup `T G = {(f γ g) g⁻¹ | g ∈ G}`.**  In the application
`G = X∞` and the right-hand side is `Subgroup.gammaSubOne`, the group of blueprint node
`commutator-eq`. -/
theorem coe_span_X_smul_top_additive :
    letI := gammaLambdaModule hG f hf γ hγ
    (((Ideal.span {(X : ℤ_[p]⟦X⟧)} • (⊤ : Submodule ℤ_[p]⟦X⟧ (Additive G))) :
        Submodule ℤ_[p]⟦X⟧ (Additive G)) : Set (Additive G))
      = Set.range fun g : G ↦ Additive.ofMul ((f γ g : G) / g) := by
  letI := additivePadicModule hG
  haveI := continuousSMul_additivePadicModule hG
  letI := additiveMulAut f
  haveI := continuousSMul_additiveMulAut f hf
  haveI := smulCommClass_additiveMulAut hG f hf
  refine Eq.trans (IwasawaAlgebra.coe_span_X_smul_top
    (IwasawaAlgebra.isUnifTopNilpotent_gammaEnd_sub_one γ hγ)
    ((IwasawaAlgebra.continuous_gammaEnd γ).sub continuous_id)) ?_
  have hd : ∀ z : Additive G,
      (IwasawaAlgebra.gammaEnd (p := p) (Z := Additive G) γ - 1) z
        = Additive.ofMul ((f γ (Additive.toMul z) : G) / Additive.toMul z) := fun _ ↦ rfl
  ext w
  simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Additive.toMul z, (hd z).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨Additive.ofMul g, hd (Additive.ofMul g)⟩

end

end ProP
