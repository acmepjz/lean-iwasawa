/-
Copyright (c) 2026 The Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.LocalCFT.LocalUnits
public import Iwasawalib.NumberTheory.CFT.AdicCompletionDecomposition

@[expose] public section

/-!
# The decomposition group acts on the local integers, with a fixed uniformizer if unramified

This file connects the abstract local theory of `Iwasawalib/NumberTheory/LocalCFT/` to the
local extensions `L_w / K_v` of a Galois extension of number fields.

* The decomposition group `D_w` preserves the `w`-adic valuation of `L_w`
  (`NumberField.valued_decomposition_smul`), so it acts on the valuation ring `O_w`.
* At an **unramified** place — `e(w|v) = 1` — a uniformizer of `K_v` remains a uniformizer of
  `L_w`, and it is fixed by `D_w` because `D_w` acts `K_v`-linearly.  This supplies the
  `G`-fixed uniformizer required by `LocalCFT.IsLocalData`.

The remaining input of `LocalCFT.IsLocalData` at an unramified place is the residue field: one
needs `O_w / 𝔪_w` to be finite and `D_w` to act on it faithfully (the inertia group is trivial
exactly when `e(w|v) = 1`).  That identification is not carried out here.

## Main statements

* `NumberField.valued_decomposition_smul`: `v (d • z) = v z` for `d ∈ D_w`.
* `NumberField.decompositionIntegersMulSemiringAction`: the action of `D_w` on `O_w`.
* `NumberField.exists_fixed_uniformizer`: a `D_w`-fixed uniformizer when `e(w|v) = 1`.
* `NumberField.exists_fixed_uniformizer_integers`: the same, inside `O_w`.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

omit [NumberField K] [w.asIdeal.LiesOver v.asIdeal] in
/-- **The decomposition group preserves the valuation of `L_w`.** -/
theorem valued_decomposition_smul (d : decompositionGroup K L w) (z : w.adicCompletion L) :
    (Valued.v (d • z) : ℤᵐ⁰) = Valued.v z := by
  rw [decomposition_smul_def, decompositionRingAut_apply, valued_adicCompletionCongr]

omit [NumberField K] [w.asIdeal.LiesOver v.asIdeal] in
/-- The valuation ring of `L_w` in the sense of `LocalCFT.integers` is the ring of integers of
the completion. -/
theorem integers_eq_adicCompletionIntegers :
    LocalCFT.integers (F := w.adicCompletion L) = w.adicCompletionIntegers L := rfl

/-- **The decomposition group acts on `O_w`.** -/
@[instance_reducible] def decompositionIntegersMulSemiringAction :
    MulSemiringAction (decompositionGroup K L w)
      (LocalCFT.integers (F := w.adicCompletion L)) :=
  LocalCFT.valuationSubringMulSemiringAction (valued_decomposition_smul w)

attribute [local instance] decompositionIntegersMulSemiringAction

omit [NumberField K] [w.asIdeal.LiesOver v.asIdeal] in
@[simp] theorem coe_decomposition_smul_integers (d : decompositionGroup K L w)
    (a : LocalCFT.integers (F := w.adicCompletion L)) :
    ((d • a : LocalCFT.integers (F := w.adicCompletion L)) : w.adicCompletion L)
      = d • (a : w.adicCompletion L) := rfl

omit [NumberField K] [w.asIdeal.LiesOver v.asIdeal] in
theorem valued_decomposition_smul_integers (d : decompositionGroup K L w)
    (a : LocalCFT.integers (F := w.adicCompletion L)) :
    (Valued.v ((d • a : LocalCFT.integers (F := w.adicCompletion L)) : w.adicCompletion L)
      : ℤᵐ⁰)
      = Valued.v ((a : LocalCFT.integers (F := w.adicCompletion L)) : w.adicCompletion L) :=
  valued_decomposition_smul w d _

/-! ## The unramified case -/

/-- **A `D_w`-fixed uniformizer at an unramified place.**  If `e(w|v) = 1`, a uniformizer of
`K_v` is a uniformizer of `L_w`, and it is fixed by the decomposition group. -/
theorem exists_fixed_uniformizer (h : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    ∃ π : w.adicCompletion L, (Valued.v π : ℤᵐ⁰) = exp (-1 : ℤ) ∧
      ∀ d : decompositionGroup K L w, d • π = π := by
  obtain ⟨c, hc⟩ := v.valuation_exists_uniformizer K
  refine ⟨adicCompletionComap K L v w ((c : K) : v.adicCompletion K), ?_,
    fun d ↦ decomposition_smul_adicCompletionComap v w d _⟩
  rw [valued_adicCompletionComap_of_ramificationIdx_eq_one K L v w h,
    valuedAdicCompletion_eq_valuation' (v := v) c]
  exact hc

/-- **A `D_w`-fixed uniformizer inside `O_w`** at an unramified place. -/
theorem exists_fixed_uniformizer_integers (h : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    ∃ π : LocalCFT.integers (F := w.adicCompletion L),
      (Valued.v ((π : LocalCFT.integers (F := w.adicCompletion L)) : w.adicCompletion L)
        : ℤᵐ⁰) = exp (-1 : ℤ) ∧
      ∀ d : decompositionGroup K L w, d • π = π := by
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer v w h
  have hmem : π ∈ LocalCFT.integers (F := w.adicCompletion L) := by
    rw [LocalCFT.mem_integer, hπ]
    rw [show (1 : ℤᵐ⁰) = exp (0 : ℤ) from exp_zero.symm, exp_le_exp]
    omega
  exact ⟨⟨π, hmem⟩, hπ, fun d ↦ Subtype.ext (hfix d)⟩

/-! ## The cohomology of `O_wˣ` at an unramified place -/

section Cohomology

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] decompositionIntegersMulSemiringAction
  IsLocalRing.residueMulSemiringAction Units.mulDistribMulActionRight

variable [Fintype (decompositionGroup K L w)]
  [FaithfulSMul (decompositionGroup K L w)
    (IsLocalRing.ResidueField (LocalCFT.integers (F := w.adicCompletion L)))]

/-- **`Ĥ¹(D_w, O_wˣ) = 0` at an unramified place.**  The only remaining hypothesis beyond
`e(w|v) = 1` is that `D_w` acts faithfully on the residue field of `O_w`, which is the
statement that the inertia group is trivial. -/
theorem exists_smul_div_of_mulNorm_eq_one_adicCompletionIntegers
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : decompositionGroup K L w} (hσ : ∀ d : decompositionGroup K L w,
      d ∈ Subgroup.zpowers σ)
    {x : (LocalCFT.integers (F := w.adicCompletion L))ˣ}
    (hx : CyclicCocycle.mulNorm (G := decompositionGroup K L w) x = 1) :
    ∃ y : (LocalCFT.integers (F := w.adicCompletion L))ˣ, σ • y / y = x := by
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer_integers v w h
  exact LocalCFT.exists_smul_div_of_mulNorm_eq_one_of_finiteResidue hσ
    (valued_decomposition_smul_integers w) hπ hfix hx

/-- **Every multiplicative 1-cocycle `D_w → O_wˣ` is a coboundary at an unramified place.** -/
theorem isMulCoboundary₁_adicCompletionIntegers
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : decompositionGroup K L w} (hσ : ∀ d : decompositionGroup K L w,
      d ∈ Subgroup.zpowers σ)
    {f : decompositionGroup K L w → (LocalCFT.integers (F := w.adicCompletion L))ˣ}
    (hf : groupCohomology.IsMulCocycle₁ f) : groupCohomology.IsMulCoboundary₁ f := by
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer_integers v w h
  exact LocalCFT.isMulCoboundary₁_of_finiteResidue hσ
    (valued_decomposition_smul_integers w) hπ hfix hf

variable [Finite (IsLocalRing.ResidueField (LocalCFT.integers (F := w.adicCompletion L)))]

/-- **`Ĥ⁰(D_w, O_wˣ) = 0` at an unramified place.** -/
theorem exists_mulNorm_eq_of_smul_eq_adicCompletionIntegers
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : decompositionGroup K L w} (hσ : ∀ d : decompositionGroup K L w,
      d ∈ Subgroup.zpowers σ)
    {x : (LocalCFT.integers (F := w.adicCompletion L))ˣ} (hx : σ • x = x) :
    ∃ y : (LocalCFT.integers (F := w.adicCompletion L))ˣ,
      CyclicCocycle.mulNorm (G := decompositionGroup K L w) y = x := by
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer_integers v w h
  exact LocalCFT.exists_mulNorm_eq_of_smul_eq_of_finiteResidue hσ
    (valued_decomposition_smul_integers w) hπ hfix hx

/-- **The local Herbrand quotient `h(O_wˣ) = 1` at an unramified place.** -/
theorem herbrand_adicCompletionIntegers_units_eq_one
    (h : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    {σ : decompositionGroup K L w} (hσ : ∀ d : decompositionGroup K L w,
      d ∈ Subgroup.zpowers σ) :
    CyclicTate.herbrand (decompositionGroup K L w)
      (Additive (LocalCFT.integers (F := w.adicCompletion L))ˣ) σ = 1 := by
  obtain ⟨π, hπ, hfix⟩ := exists_fixed_uniformizer_integers v w h
  exact LocalCFT.herbrand_units_eq_one hσ (valued_decomposition_smul_integers w) hπ hfix

end Cohomology

end NumberField
