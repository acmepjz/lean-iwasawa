/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.IdeleShortExact
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

/-!
# Passing from the Galois group to its subgroups

The axioms of a class formation are quantified over *all* subgroups `H` of `G = Gal(L/K)`, so
every statement about `H¹(G, ·)` has to be available for `H¹(H, ·)` as well.  By the Galois
correspondence `H` is the Galois group of `L` over the fixed field `L^H`, which is again a
number field, so no new mathematics is needed: the statements for the base field `L^H` are the
statements for `H`, transported along `IntermediateField.subgroupEquivAlgEquiv`.

This file provides that transport.  The essential observation, which is `rfl`, is that the
action of `h : H` on any `Gal(L/K)`-module obtained from an action of `RingAut L` agrees with
the action of the corresponding element of `Gal(L/L^H)`.

## Main definitions

* `groupCohomology.mulDistribMapIso`: `Hⁿ(G, M) ≅ Hⁿ(G', M)` for a group isomorphism
  `G ≃* G'` compatible with two actions on the same commutative group `M`.
* `NumberField.subgroupUnitsIso`, `NumberField.subgroupIdeleIso`,
  `NumberField.subgroupIdeleClassIso`: `Hⁿ(H, ·) ≅ Hⁿ(Gal(L/L^H), ·)` for `Lˣ`, `𝕀_L`, `C_L`.

## Main statements

* `NumberField.isZero_H1_subgroup_units`: `H¹(H, Lˣ) = 0` for *every* subgroup `H` of
  `Gal(L/K)` — Hilbert 90 for all the subgroups at once.
* `NumberField.isZero_H1_subgroup_repIdeleClass_of`: `H¹(H, C_L) = 0` under the two hypotheses
  of `NumberField.isZero_H1_repIdeleClass_of` taken over the fixed field `L^H`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits IsDedekindDomain IntermediateField

attribute [local instance] Units.mulDistribMulActionRight
  NumberField.galIdeleMulDistribMulAction NumberField.galIdeleClassMulDistribMulAction

namespace groupCohomology

variable {G G' M : Type} [Group G] [Group G'] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction G' M]

/-- Two actions on the same commutative group `M` which correspond under a group isomorphism
`e : G ≃* G'` have the same cohomology. -/
def mulDistribMapIso (e : G ≃* G') (he : ∀ (g : G) (m : M), e g • m = g • m) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction G M) n ≅
      groupCohomology (Rep.ofMulDistribMulAction G' M) n :=
  mapIso e (AddEquiv.refl (Additive M)).toIntLinearEquivOfModule
    (fun g ↦ LinearMap.ext fun m ↦
      (congrArg Additive.ofMul (he g (Additive.toMul (show Additive M from m)))).symm) n

end groupCohomology

namespace NumberField

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L))

omit [IsGalois K L] in
/-- The action of a subgroup `H ≤ Gal(L/K)` on `Lˣ` is the action of `Gal(L/L^H)`. -/
theorem subgroupEquivAlgEquiv_smul_units (h : H) (x : Lˣ) :
    (subgroupEquivAlgEquiv H h) • x = h • x := rfl

omit [IsGalois K L] in
/-- The action of a subgroup `H ≤ Gal(L/K)` on `𝕀_L` is the action of `Gal(L/L^H)`. -/
theorem subgroupEquivAlgEquiv_smul_idele (h : H) (u : IdeleGroup (𝓞 L) L) :
    (subgroupEquivAlgEquiv H h) • u = h • u := rfl

omit [IsGalois K L] in
/-- The action of a subgroup `H ≤ Gal(L/K)` on `C_L` is the action of `Gal(L/L^H)`. -/
theorem subgroupEquivAlgEquiv_smul_ideleClass (h : H) (c : IdeleClassGroup (𝓞 L) L) :
    (subgroupEquivAlgEquiv H h) • c = h • c := rfl

/-- `Hⁿ(H, Lˣ) ≅ Hⁿ(Gal(L/L^H), Lˣ)`. -/
def subgroupUnitsIso (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction H Lˣ) n ≅
      groupCohomology (repUnits (fixedField H) L) n :=
  groupCohomology.mulDistribMapIso (subgroupEquivAlgEquiv H)
    (subgroupEquivAlgEquiv_smul_units H) n

/-- `Hⁿ(H, 𝕀_L) ≅ Hⁿ(Gal(L/L^H), 𝕀_L)`. -/
def subgroupIdeleIso (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction H (IdeleGroup (𝓞 L) L)) n ≅
      groupCohomology (repIdele (fixedField H) L) n :=
  groupCohomology.mulDistribMapIso (subgroupEquivAlgEquiv H)
    (subgroupEquivAlgEquiv_smul_idele H) n

/-- `Hⁿ(H, C_L) ≅ Hⁿ(Gal(L/L^H), C_L)`. -/
def subgroupIdeleClassIso (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction H (IdeleClassGroup (𝓞 L) L)) n ≅
      groupCohomology (repIdeleClass (fixedField H) L) n :=
  groupCohomology.mulDistribMapIso (subgroupEquivAlgEquiv H)
    (subgroupEquivAlgEquiv_smul_ideleClass H) n

omit [IsGalois K L] in
/-- **Hilbert 90 for every subgroup of the Galois group**: `H¹(H, Lˣ) = 0` for every
`H ≤ Gal(L/K)`. -/
theorem isZero_H1_subgroup_units :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction H Lˣ) 1) :=
  (isZero_H1_repUnits (fixedField H) L).of_iso (subgroupUnitsIso H 1)

omit [IsGalois K L] in
/-- **The first axiom of a class formation, for a subgroup.**  If `H¹(Gal(L/L^H), 𝕀_L) = 0` and
`H²(Gal(L/L^H), Lˣ) ⟶ H²(Gal(L/L^H), 𝕀_L)` is injective, then `H¹(H, C_L) = 0`. -/
theorem isZero_H1_subgroup_repIdeleClass_of
    (hIdele : IsZero (groupCohomology (repIdele (fixedField H) L) 1))
    (hmono : Mono ((groupCohomology.functor ℤ (L ≃ₐ[fixedField H] L) 2).map
      (ideleShortComplex (fixedField H) L).f)) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction H (IdeleClassGroup (𝓞 L) L)) 1) :=
  (isZero_H1_repIdeleClass_of (fixedField H) L hIdele hmono).of_iso (subgroupIdeleClassIso H 1)

end NumberField
