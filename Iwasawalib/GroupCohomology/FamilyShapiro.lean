/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.EquivariantFamily
public import Iwasawalib.GroupCohomology.Shapiro

@[expose] public section

/-!
# Shapiro's lemma for a transitive equivariant family

Combining `EquivariantFamily.equivRcoind` (a transitive equivariant family of rings is an
induced module) with Shapiro's lemma gives, for a group `G` acting transitively on `Ω` and a
compatible family of rings `M : Ω → Type`,

`Hⁿ(G, ∏ w : Ω, M w) ≅ Hⁿ(Stab_G(w₀), M w₀)`

for every base point `w₀ : Ω`, and the same for the unit groups.

Everything is stated in `Type`, as Mathlib's `groupCohomology` requires the coefficient ring
`ℤ`, the group and the module to lie in one universe.

## Main definitions

* `EquivariantFamily.shapiro`: `Hⁿ(G, ∏ w, M w) ≅ Hⁿ(Stab_G(w₀), M w₀)`.
* `EquivariantFamily.shapiroUnits`: `Hⁿ(G, (∏ w, M w)ˣ) ≅ Hⁿ(Stab_G(w₀), (M w₀)ˣ)`.
-/

noncomputable section

open MulAction CategoryTheory

attribute [local instance] Units.mulDistribMulActionRight

namespace EquivariantFamily

variable {G Ω : Type} [Group G] [MulAction G Ω] {M : Ω → Type} [∀ w, CommRing (M w)]
  (F : EquivariantFamily G Ω M) {w₀ : Ω}
  [MulSemiringAction G (∀ w : Ω, M w)] [MulSemiringAction (stabilizer G w₀) (M w₀)]

variable (G M) in
/-- The product `∏ w : Ω, M w` as a `ℤ`-linear `G`-representation. -/
abbrev repPi : Rep ℤ G := Rep.ofDistribMulAction ℤ G (∀ w : Ω, M w)

variable (G M) in
/-- The factor `M w₀` as a `ℤ`-linear representation of the stabiliser of `w₀`. -/
abbrev repFactor (w₀ : Ω) [MulSemiringAction (stabilizer G w₀) (M w₀)] :
    Rep ℤ (stabilizer G w₀) :=
  Rep.ofDistribMulAction ℤ _ (M w₀)

variable (G M) in
/-- The unit group `(∏ w : Ω, M w)ˣ` as a `ℤ`-linear `G`-representation. -/
abbrev repPiUnits : Rep ℤ G := Rep.ofMulDistribMulAction G (∀ w : Ω, M w)ˣ

variable (G M) in
/-- The unit group `(M w₀)ˣ` as a `ℤ`-linear representation of the stabiliser of `w₀`. -/
abbrev repFactorUnits (w₀ : Ω) [MulSemiringAction (stabilizer G w₀) (M w₀)] :
    Rep ℤ (stabilizer G w₀) :=
  Rep.ofMulDistribMulAction _ (M w₀)ˣ

variable [IsPretransitive G Ω] (hstab : F.IsStabilizerAction (w₀ := w₀))

include hstab

/-- The product is the coinduced module, as an additive isomorphism. -/
def piAddEquivRcoindV :
    (repPi G M).V ≃+ (Rep.rcoind (stabilizer G w₀) (repFactor G M w₀)).V :=
  (F.equivRcoind hstab).toAddEquiv.trans (Subring.rcoindAddEquivRcoindV _ _)

theorem piAddEquivRcoindV_equivariant (hpi : F.IsPiAction) (σ : G) (x : (repPi G M).V) :
    F.piAddEquivRcoindV hstab ((repPi G M).ρ σ x) =
      (Rep.rcoind (stabilizer G w₀) (repFactor G M w₀)).ρ σ (F.piAddEquivRcoindV hstab x) :=
  Subtype.ext (funext fun g ↦
    (congrArg (fun z : Subring.rcoind (stabilizer G w₀) (M w₀) ↦ (z : G → M w₀) g)
      (F.equivRcoind_smul hstab hpi σ x)).trans (Subring.rcoind_smul_apply σ _ g))

/-- **Shapiro's lemma for a transitive equivariant family of rings**:
`Hⁿ(G, ∏ w : Ω, M w) ≅ Hⁿ(Stab_G(w₀), M w₀)`. -/
def shapiro (hpi : F.IsPiAction) (n : ℕ) :
    groupCohomology (repPi G M) n ≅ groupCohomology (repFactor G M w₀) n :=
  groupCohomology.shapiroOfEquiv _ _
    (F.piAddEquivRcoindV hstab).toIntLinearEquivOfModule
    (F.piAddEquivRcoindV_equivariant hstab hpi) n

/-- The unit group of the product is the coinduced module of the unit groups, as an additive
isomorphism. -/
def piUnitsAddEquivRcoindV :
    (repPiUnits G M).V ≃+ (Rep.rcoind (stabilizer G w₀) (repFactorUnits G M w₀)).V :=
  (MulEquiv.toAdditive (Units.mapEquiv (F.equivRcoind hstab).toMulEquiv)).trans
    ((MulEquiv.toAdditive (Subring.rcoindUnitsEquiv _ _)).trans
      (Subgroup.rcoindMulAddEquivRcoindV _ _))

theorem piUnitsAddEquivRcoindV_equivariant (hpi : F.IsPiAction) (σ : G)
    (x : (repPiUnits G M).V) :
    F.piUnitsAddEquivRcoindV hstab ((repPiUnits G M).ρ σ x) =
      (Rep.rcoind (stabilizer G w₀) (repFactorUnits G M w₀)).ρ σ
        (F.piUnitsAddEquivRcoindV hstab x) :=
  Subtype.ext (funext fun g ↦ Units.ext
    ((congrArg (fun z : Subring.rcoind (stabilizer G w₀) (M w₀) ↦ (z : G → M w₀) g)
      (F.equivRcoind_smul hstab hpi σ _)).trans (Subring.rcoind_smul_apply σ _ g)))

/-- **Shapiro's lemma for the units of a transitive equivariant family of rings**:
`Hⁿ(G, (∏ w : Ω, M w)ˣ) ≅ Hⁿ(Stab_G(w₀), (M w₀)ˣ)`. -/
def shapiroUnits (hpi : F.IsPiAction) (n : ℕ) :
    groupCohomology (repPiUnits G M) n ≅ groupCohomology (repFactorUnits G M w₀) n :=
  groupCohomology.shapiroOfEquiv _ _
    (F.piUnitsAddEquivRcoindV hstab).toIntLinearEquivOfModule
    (F.piUnitsAddEquivRcoindV_equivariant hstab hpi) n

end EquivariantFamily
