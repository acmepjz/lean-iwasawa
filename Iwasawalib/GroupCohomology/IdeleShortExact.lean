/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Hilbert90
public import Iwasawalib.GroupCohomology.MulDistribShortExact
public import Iwasawalib.NumberTheory.CFT.AdeleCongr

@[expose] public section

/-!
# The defining short exact sequence of the idele class group

For a finite Galois extension `L / K` of number fields, the sequence

`1 ⟶ Lˣ ⟶ 𝕀_L ⟶ C_L ⟶ 1`

is a short exact sequence of `Gal(L/K)`-modules.  This file builds it as a short exact sequence
in `Rep ℤ Gal(L/K)`, so that Mathlib's long exact sequence in group cohomology applies to it,
and records the two consequences that are available at this point:

* Hilbert 90 gives `H¹(Gal(L/K), Lˣ) = 0`, so `H¹(Gal(L/K), 𝕀_L) ⟶ H¹(Gal(L/K), C_L)` is the
  beginning of the long exact sequence;
* if moreover `H¹(Gal(L/K), 𝕀_L) = 0` and `H²(Gal(L/K), Lˣ) ⟶ H²(Gal(L/K), 𝕀_L)` is injective,
  then `H¹(Gal(L/K), C_L) = 0`, the first axiom of a class formation.

## Main definitions

* `NumberField.repUnits`, `NumberField.repIdele`, `NumberField.repIdeleClass`: `Lˣ`, `𝕀_L`
  and `C_L` as `ℤ`-linear `Gal(L/K)`-representations.
* `NumberField.ideleShortComplex`: the short complex `Lˣ ⟶ 𝕀_L ⟶ C_L` in `Rep ℤ Gal(L/K)`.

## Main statements

* `NumberField.ideleShortComplex_shortExact`: it is short exact.
* `NumberField.isZero_H1_units`: `H¹(Gal(L/K), Lˣ) = 0` (Hilbert 90).
* `NumberField.isZero_H1_ideleClass_of`: the criterion for `H¹(Gal(L/K), C_L) = 0`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits IsDedekindDomain

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction

namespace NumberField

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-! ## The three representations -/

/-- `Lˣ` as a `ℤ`-linear `Gal(L/K)`-representation. -/
abbrev repUnits : Rep ℤ (L ≃ₐ[K] L) := Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ

/-- The idele group `𝕀_L` as a `ℤ`-linear `Gal(L/K)`-representation. -/
abbrev repIdele : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup (𝓞 L) L)

/-- The idele class group `C_L` as a `ℤ`-linear `Gal(L/K)`-representation. -/
abbrev repIdeleClass : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup (𝓞 L) L)

/-! ## Equivariance of the two maps -/

variable {K L}

/-- The embedding of the principal ideles is `Gal(L/K)`-equivariant. -/
theorem principalEmbedding_smul (σ : L ≃ₐ[K] L) (x : Lˣ) :
    IdeleGroup.principalEmbedding (𝓞 L) L (σ • x) =
      σ • IdeleGroup.principalEmbedding (𝓞 L) L x := by
  refine Units.ext ?_
  show algebraMap L (AdeleRing (𝓞 L) L) (σ (x : L)) = _
  rw [show σ • IdeleGroup.principalEmbedding (𝓞 L) L x
      = ideleAut (galToRingAut K L σ) (IdeleGroup.principalEmbedding (𝓞 L) L x) from rfl,
    ideleAut_principalEmbedding]
  rfl

/-- The quotient map to the idele class group is `Gal(L/K)`-equivariant. -/
theorem mk_smul (σ : L ≃ₐ[K] L) (u : IdeleGroup (𝓞 L) L) :
    IdeleClassGroup.mk (𝓞 L) L (σ • u) = σ • IdeleClassGroup.mk (𝓞 L) L u :=
  (galIdeleClassAut_mk σ u).symm

variable (K L)

/-! ## The short exact sequence -/

/-- The short complex `Lˣ ⟶ 𝕀_L ⟶ C_L` in `Rep ℤ Gal(L/K)`. -/
def ideleShortComplex : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  Rep.mulShortComplex (M := L ≃ₐ[K] L) (IdeleGroup.principalEmbedding (𝓞 L) L)
    (fun σ x ↦ principalEmbedding_smul σ x) (IdeleClassGroup.mk (𝓞 L) L)
    (fun σ u ↦ mk_smul σ u) (fun x ↦ IdeleClassGroup.mk_principalEmbedding (𝓞 L) L x)

@[simp] theorem ideleShortComplex_X₁ : (ideleShortComplex K L).X₁ = repUnits K L := rfl
@[simp] theorem ideleShortComplex_X₂ : (ideleShortComplex K L).X₂ = repIdele K L := rfl
@[simp] theorem ideleShortComplex_X₃ : (ideleShortComplex K L).X₃ = repIdeleClass K L := rfl

/-- **`1 ⟶ Lˣ ⟶ 𝕀_L ⟶ C_L ⟶ 1` is a short exact sequence of `Gal(L/K)`-modules.** -/
theorem ideleShortComplex_shortExact : (ideleShortComplex K L).ShortExact :=
  Rep.mulShortComplex_shortExact _ _ _ _ _
    (IdeleGroup.principalEmbedding_injective (𝓞 L) L)
    (IdeleClassGroup.mk_surjective (𝓞 L) L)
    (fun _ hu ↦ (IdeleClassGroup.mk_eq_one_iff (𝓞 L) L).1 hu)

/-! ## Hilbert 90 and the vanishing criterion -/

omit [NumberField L] in
/-- `Gal(L/K)` acts faithfully on `L`. -/
theorem galois_smul_injective :
    Function.Injective fun (g : L ≃ₐ[K] L) ↦ (fun x : L ↦ g • x) :=
  fun _ _ h ↦ AlgEquiv.ext fun x ↦ congrFun h x

section Hilbert90

variable [FiniteDimensional K L]

omit [NumberField L] in
/-- **Hilbert 90 for the global field**: `H¹(Gal(L/K), Lˣ) = 0`. -/
theorem isZero_H1_repUnits : IsZero (groupCohomology (repUnits K L) 1) := by
  have : Subsingleton (groupCohomology (repUnits K L) 1) :=
    groupCohomology.subsingleton_H1_units (galois_smul_injective K L)
  exact (IsZero.iff_id_eq_zero _).2 <| ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    Subsingleton.elim _ _

end Hilbert90

/-- **The criterion for the first axiom of a class formation.**  If `H¹(Gal(L/K), 𝕀_L) = 0` and
the map `H²(Gal(L/K), Lˣ) ⟶ H²(Gal(L/K), 𝕀_L)` is injective, then `H¹(Gal(L/K), C_L) = 0`.

Both hypotheses are genuine theorems of global class field theory and are *not* proved here:
the first is the vanishing of `H¹` of the restricted product of the local unit groups, the
second is the injectivity of the map from the Brauer group of `L/K` into the sum of the local
Brauer groups. -/
theorem isZero_H1_repIdeleClass_of
    (hIdele : IsZero (groupCohomology (repIdele K L) 1))
    (hmono : Mono ((groupCohomology.functor ℤ (L ≃ₐ[K] L) 2).map (ideleShortComplex K L).f)) :
    IsZero (groupCohomology (repIdeleClass K L) 1) :=
  groupCohomology.isZero_of_isZero_of_mono (ideleShortComplex_shortExact K L) 1 hIdele hmono

end NumberField
