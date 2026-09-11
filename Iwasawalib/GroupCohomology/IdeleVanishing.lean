/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.IdeleShortExact
public import Iwasawalib.GroupCohomology.InfinitePlaceHilbert90
public import Iwasawalib.GroupCohomology.ProductVanishing

@[expose] public section

/-!
# `H¹(Gal(L/K), 𝕀_L)` reduces to the finite ideles

The idele group of `L` splits as `𝕀_L = (𝔸_L^∞)^× × (𝔸_L^f)^×`, and the archimedean factor is a
*finite* product of the semilocal factors `∏_{w ∣ v} L_w^×`, whose `H¹` vanishes by Hilbert 90
and Shapiro's lemma (`Iwasawalib/GroupCohomology/InfinitePlaceHilbert90.lean`).  Since `H¹`
commutes with products (`Iwasawalib/GroupCohomology/ProductVanishing.lean`), the archimedean
half of the first fundamental inequality is unconditional:

`H¹(Gal(L/K), (𝔸_L^∞)^×) = 0`,

and the vanishing `H¹(Gal(L/K), 𝕀_L) = 0` is *equivalent* to the vanishing for the finite
ideles `(𝔸_L^f)^×`.  The latter is the restricted-product statement, which additionally needs
`H¹(D_w, O_w^×) = 0` for almost all `w`; it is not proved here.

## Main definitions

* `NumberField.galInfiniteAdeleMulSemiringAction`: `𝔸_L^∞` as a `Gal(L/K)`-ring.
* `NumberField.infiniteIdeleEquivPi`: `(𝔸_L^∞)^× ≃* ∏_v (∏_{w ∣ v} L_w^×)`.
* `NumberField.ideleEquivProd`: `𝕀_L ≃* (𝔸_L^∞)^× × (𝔸_L^f)^×`.

## Main statements

* `NumberField.isZero_H1_infiniteIdele`: `H¹(Gal(L/K), (𝔸_L^∞)^×) = 0`.
* `NumberField.isZero_H1_repIdele_iff`: `H¹(Gal(L/K), 𝕀_L) = 0` if and only if
  `H¹(Gal(L/K), (𝔸_L^f)^×) = 0`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits IsDedekindDomain MulAction
open NumberField.InfiniteAdeleRing

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction

namespace NumberField

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- `𝔸_L^∞` as a `Gal(L/K)`-ring. -/
@[instance_reducible] def galInfiniteAdeleMulSemiringAction :
    MulSemiringAction (L ≃ₐ[K] L) (InfiniteAdeleRing L) :=
  MulSemiringAction.compHom _ (infiniteAdeleAut.comp (galToRingAut K L))

attribute [local instance] galInfiniteAdeleMulSemiringAction

variable {K L}

omit [NumberField K] [NumberField L] in
theorem galInfiniteAdele_smul_def (σ : L ≃ₐ[K] L) (x : InfiniteAdeleRing L) :
    σ • x = infiniteAdeleMap (σ : L ≃+* L) x := rfl

variable (K L)

/-! ## The archimedean ideles are a product of the semilocal factors -/

/-- **The archimedean ideles are the product of the semilocal unit groups.**
`(𝔸_L^∞)^× ≃ ∏_{v ∣ ∞} (∏_{w ∣ v} L_w)^×`. -/
def infiniteIdeleEquivPi :
    (InfiniteAdeleRing L)ˣ ≃* ∀ v : InfinitePlace K, (InfiniteLocalProduct L v)ˣ :=
  (Units.mapEquiv (semilocalEquiv (K := K) L).toMulEquiv).trans MulEquiv.piUnits

variable {K L}

omit [NumberField K] [NumberField L] in
theorem infiniteIdeleEquivPi_smul (σ : L ≃ₐ[K] L) (u : (InfiniteAdeleRing L)ˣ) :
    infiniteIdeleEquivPi K L (σ • u) = σ • infiniteIdeleEquivPi K L u :=
  funext fun _ ↦ Units.ext rfl

variable [IsGalois K L]

/-- **`H¹` of the archimedean ideles vanishes**: `H¹(Gal(L/K), (𝔸_L^∞)^×) = 0`.  This is the
archimedean half of the first fundamental inequality, and it is unconditional: the infinite
adeles are an honest product of the semilocal factors, and `H¹` of each of those vanishes by
Hilbert 90 and Shapiro's lemma. -/
theorem isZero_H1_infiniteIdele :
    IsZero (groupCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (InfiniteAdeleRing L)ˣ) 1) := by
  refine groupCohomology.isZero_H1_of_mulEquiv (infiniteIdeleEquivPi K L)
    infiniteIdeleEquivPi_smul (groupCohomology.isZero_H1_pi fun v ↦ ?_)
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (Fibre L v))
  have : Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (InfiniteLocalProduct L v)ˣ) 1) :=
    ⟨fun x y ↦ by
      rw [H1_infiniteLocalUnits_eq_zero w₀ x, H1_infiniteLocalUnits_eq_zero w₀ y]⟩
  exact ModuleCat.isZero_of_subsingleton _

variable (K L)

/-! ## The splitting of the ideles -/

/-- The idele group splits as `𝕀_L ≃ (𝔸_L^∞)^× × (𝔸_L^f)^×`. -/
def ideleEquivProd (L : Type) [Field L] [NumberField L] :
    IdeleGroup (𝓞 L) L ≃* (InfiniteAdeleRing L)ˣ × (FiniteAdeleRing (𝓞 L) L)ˣ :=
  (Units.mapEquiv (AdeleRing.prodEquiv (𝓞 L) L).toMulEquiv).trans MulEquiv.prodUnits

variable {K L}

omit [NumberField K] [IsGalois K L] in
theorem ideleEquivProd_smul (σ : L ≃ₐ[K] L) (u : IdeleGroup (𝓞 L) L) :
    ideleEquivProd L (σ • u) = σ • ideleEquivProd L u :=
  Prod.ext (Units.ext rfl) (Units.ext rfl)

variable (K L)

/-- **The vanishing of `H¹` of the ideles is exactly the vanishing for the finite ideles.** -/
theorem isZero_H1_repIdele_iff :
    IsZero (groupCohomology (repIdele K L) 1) ↔
      IsZero (groupCohomology
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (FiniteAdeleRing (𝓞 L) L)ˣ) 1) := by
  constructor
  · intro h
    exact groupCohomology.isZero_H1_of_prod_right
      (h.of_iso (groupCohomology.mulDistribCongr (ideleEquivProd L)
        (ideleEquivProd_smul (K := K)) 1).symm)
  · intro h
    exact groupCohomology.isZero_H1_of_mulEquiv (ideleEquivProd L)
      (ideleEquivProd_smul (K := K))
      (groupCohomology.isZero_H1_prod isZero_H1_infiniteIdele h)

end NumberField
