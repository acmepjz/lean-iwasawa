/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.GroupCohomology.Shapiro
public import Iwasawalib.NumberTheory.CFT.FiniteAdeleCongr

@[expose] public section

/-!
# Shapiro's lemma for the local factors of the adeles

Let `L / K` be a finite Galois extension of number fields, `v` a finite place of `K` and `w₀`
a place of `L` above `v`.  `Iwasawalib/NumberTheory/CFT/FiniteAdeleCongr.lean` proves that the
local factor of the adeles of `L` at `v`,

`∏_{w ∣ v} L_w`,

is, `Gal(L/K)`-equivariantly, the induced module `Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`, realised as
the ring `IndLocal K L w₀` of `D_{w₀}`-equivariant functions `Gal(L/K) → L_{w₀}`.  That is
exactly the right-equivariant model `Representation.rcoind` of
`Iwasawalib/GroupCohomology/Induced.lean`, so Shapiro's lemma applies and gives

`Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w) ≅ Hⁿ(D_{w₀}, L_{w₀})`,

together with its multiplicative counterpart

`Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w^×) ≅ Hⁿ(D_{w₀}, L_{w₀}^×)`,

which is the idele-level input to the two fundamental inequalities of class field theory.

Everything is stated for number fields in `Type`: Mathlib's `groupCohomology` requires the
coefficient ring, the group and the module to live in the same universe, and the coefficient
ring here is `ℤ`.

## Main definitions

* `NumberField.repLocalProduct`, `NumberField.repAdicCompletion`: `∏_{w ∣ v} L_w` as a
  `ℤ`-linear `Gal(L/K)`-representation, and `L_{w₀}` as a `ℤ`-linear `D_{w₀}`-representation.
* `NumberField.localProductShapiro`: `Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w) ≅ Hⁿ(D_{w₀}, L_{w₀})`.
* `NumberField.repLocalProductUnits`, `NumberField.repAdicCompletionUnits`,
  `NumberField.localProductUnitsShapiro`: the same for the unit groups.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

attribute [local instance] Units.mulDistribMulActionRight

namespace NumberField

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)} {w₀ : HeightOneSpectrum (𝓞 L)}

/-! ## The representations -/

variable (K L) in
/-- The local field `L_{w₀}` as a `ℤ`-linear representation of the decomposition group
`D_{w₀} ≤ Gal(L/K)`. -/
abbrev repAdicCompletion (w₀ : HeightOneSpectrum (𝓞 L)) :
    Rep ℤ (decompositionGroup K L w₀) :=
  Rep.ofDistribMulAction ℤ _ (w₀.adicCompletion L)

variable (K L) in
/-- The local factor `∏_{w ∣ v} L_w` of the adeles of `L` at `v`, as a `ℤ`-linear
representation of `Gal(L/K)`. -/
abbrev repLocalProduct (v : HeightOneSpectrum (𝓞 K)) : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction ℤ _ (LocalProduct K L v)

/-! ## `IndLocal` is the right-equivariant coinduced module -/

/-- `IndLocal K L w₀`, the ring of `D_{w₀}`-equivariant functions `Gal(L/K) → L_{w₀}`, is the
underlying module of the coinduced representation `Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`.  The two
are the same set of functions, so this is the identity map. -/
def indLocalAddEquivRcoindV (w₀ : HeightOneSpectrum (𝓞 L)) :
    IndLocal K L w₀ ≃+ (Rep.rcoind (decompositionGroup K L w₀) (repAdicCompletion K L w₀)).V where
  toFun F := ⟨F.1, fun g d ↦ F.2 g d⟩
  invFun F := ⟨F.1, fun g d ↦ F.2 g d⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [NumberField K] [IsGalois K L] in
@[simp]
lemma indLocalAddEquivRcoindV_apply_val (F : IndLocal K L w₀) (g : L ≃ₐ[K] L) :
    (indLocalAddEquivRcoindV w₀ F).1 g = (F : (L ≃ₐ[K] L) → w₀.adicCompletion L) g := rfl

omit [NumberField K] [IsGalois K L] in
lemma indLocalAddEquivRcoindV_equivariant (σ : L ≃ₐ[K] L) (F : IndLocal K L w₀) :
    indLocalAddEquivRcoindV w₀ (σ • F) =
      (Rep.rcoind (decompositionGroup K L w₀) (repAdicCompletion K L w₀)).ρ σ
        (indLocalAddEquivRcoindV w₀ F) := rfl

/-- The composite `Gal(L/K)`-equivariant additive isomorphism
`∏_{w ∣ v} L_w ≃ Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`. -/
def localProductAddEquivRcoindV (hw₀ : w₀ ∈ placesOver K L v) :
    (repLocalProduct K L v).V ≃+
      (Rep.rcoind (decompositionGroup K L w₀) (repAdicCompletion K L w₀)).V :=
  (localProductEquivIndLocal hw₀).toAddEquiv.trans (indLocalAddEquivRcoindV w₀)

lemma localProductAddEquivRcoindV_equivariant (hw₀ : w₀ ∈ placesOver K L v) (σ : L ≃ₐ[K] L)
    (x : LocalProduct K L v) :
    localProductAddEquivRcoindV hw₀ ((repLocalProduct K L v).ρ σ x) =
      (Rep.rcoind (decompositionGroup K L w₀) (repAdicCompletion K L w₀)).ρ σ
        (localProductAddEquivRcoindV hw₀ x) := by
  show indLocalAddEquivRcoindV w₀ (localProductEquivIndLocal hw₀ (σ • x)) = _
  rw [localProductEquivIndLocal_smul hw₀ σ x]
  exact indLocalAddEquivRcoindV_equivariant σ _

/-! ## Shapiro's lemma for the local factor -/

/-- **Shapiro's lemma for the local factors of the adeles.**  For a finite Galois extension
`L / K` of number fields, a finite place `v` of `K` and a place `w₀` of `L` above `v`,
`Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w) ≅ Hⁿ(D_{w₀}, L_{w₀})` for every `n`. -/
def localProductShapiro (hw₀ : w₀ ∈ placesOver K L v) (n : ℕ) :
    groupCohomology (repLocalProduct K L v) n ≅
      groupCohomology (repAdicCompletion K L w₀) n :=
  groupCohomology.shapiroOfEquiv _ _
    (localProductAddEquivRcoindV hw₀).toIntLinearEquivOfModule
    (localProductAddEquivRcoindV_equivariant hw₀) n

/-! ## The multiplicative version: the local units -/

variable (K L) in
/-- The unit group `L_{w₀}^×` of the local field, as a `ℤ`-linear representation of the
decomposition group `D_{w₀}`. -/
abbrev repAdicCompletionUnits (w₀ : HeightOneSpectrum (𝓞 L)) :
    Rep ℤ (decompositionGroup K L w₀) :=
  Rep.ofMulDistribMulAction _ (w₀.adicCompletion L)ˣ

variable (K L) in
/-- The group `(∏_{w ∣ v} L_w)^× = ∏_{w ∣ v} L_w^×` of local units at `v`, as a `ℤ`-linear
representation of `Gal(L/K)`. -/
abbrev repLocalProductUnits (v : HeightOneSpectrum (𝓞 K)) : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction _ (LocalProduct K L v)ˣ

/-- The units of `IndLocal K L w₀` are the `D_{w₀}`-equivariant functions
`Gal(L/K) → L_{w₀}^×`: `IndLocal` is the coinduced *ring*, and the unit group of a coinduced
ring is the coinduced group of the units (`Subring.rcoindUnitsEquiv`). -/
def indLocalUnitsEquiv (w₀ : HeightOneSpectrum (𝓞 L)) :
    (IndLocal K L w₀)ˣ ≃* Subgroup.rcoindMul (decompositionGroup K L w₀)
      (w₀.adicCompletion L)ˣ :=
  Subring.rcoindUnitsEquiv _ _

/-- The unit group of `Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}`, written additively, is the coinduced
module of `L_{w₀}^×`. -/
def indLocalUnitsAddEquivRcoindV (w₀ : HeightOneSpectrum (𝓞 L)) :
    Additive (IndLocal K L w₀)ˣ ≃+
      (Rep.rcoind (decompositionGroup K L w₀) (repAdicCompletionUnits K L w₀)).V :=
  (MulEquiv.toAdditive (indLocalUnitsEquiv w₀)).trans
    (Subgroup.rcoindMulAddEquivRcoindV _ _)

/-- The composite `Gal(L/K)`-equivariant isomorphism
`(∏_{w ∣ v} L_w)^× ≃ Ind_{D_{w₀}}^{Gal(L/K)} L_{w₀}^×`, written additively. -/
def localProductUnitsAddEquivRcoindV (hw₀ : w₀ ∈ placesOver K L v) :
    (repLocalProductUnits K L v).V ≃+
      (Rep.rcoind (decompositionGroup K L w₀) (repAdicCompletionUnits K L w₀)).V :=
  (MulEquiv.toAdditive (Units.mapEquiv (localProductEquivIndLocal hw₀).toMulEquiv)).trans
    (indLocalUnitsAddEquivRcoindV w₀)

lemma localProductUnitsAddEquivRcoindV_equivariant (hw₀ : w₀ ∈ placesOver K L v)
    (σ : L ≃ₐ[K] L) (x : (repLocalProductUnits K L v).V) :
    localProductUnitsAddEquivRcoindV hw₀ ((repLocalProductUnits K L v).ρ σ x) =
      (Rep.rcoind (decompositionGroup K L w₀) (repAdicCompletionUnits K L w₀)).ρ σ
        (localProductUnitsAddEquivRcoindV hw₀ x) :=
  Subtype.ext (funext fun g ↦ Units.ext
    ((congrArg (fun F : IndLocal K L w₀ ↦ (F : (L ≃ₐ[K] L) → w₀.adicCompletion L) g)
      (localProductEquivIndLocal_smul hw₀ σ _)).trans (indLocal_smul_apply σ _ g)))

/-- **Shapiro's lemma for the local units.**  For a finite Galois extension `L / K` of number
fields, a finite place `v` of `K` and a place `w₀` of `L` above `v`,
`Hⁿ(Gal(L/K), ∏_{w ∣ v} L_w^×) ≅ Hⁿ(D_{w₀}, L_{w₀}^×)` for every `n`.  This is the idele-level
input to the fundamental inequalities of class field theory. -/
def localProductUnitsShapiro (hw₀ : w₀ ∈ placesOver K L v) (n : ℕ) :
    groupCohomology (repLocalProductUnits K L v) n ≅
      groupCohomology (repAdicCompletionUnits K L w₀) n :=
  groupCohomology.shapiroOfEquiv _ _
    (localProductUnitsAddEquivRcoindV hw₀).toIntLinearEquivOfModule
    (localProductUnitsAddEquivRcoindV_equivariant hw₀) n

end NumberField
