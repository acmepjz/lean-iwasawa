/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.RamifiedFamily
public import Iwasawalib.NumberTheory.ZpExtension.Ln
public import Iwasawalib.NumberTheory.ZpExtension.LinearDisjoint

@[expose] public section

/-!
# An everywhere-unramified, totally ramified intermediate field is the base

## Main statements

* `IntermediateField.intermediateField_eq_bot_of_totallyRamified_of_isUnramifiedEverywhere`:
  **Warning**: its hypothesis `htot` is satisfiable only when the conclusion already holds; see
  its docstring, and use
  `IntermediateField.eq_bot_of_isUnramifiedEverywhere_of_inertiaSubgroup_eq_top`
  (`Iwasawalib/NumberTheory/ZpExtension/FiniteSubalgebraLinearDisjoint.lean`) instead.
* `IntermediateField.linearDisjoint_of_intermediateField_eq_bot`: `A.LinearDisjoint B` when
  `B = ⊥`.
-/

open IntermediateField

universe u v

namespace IntermediateField

/-- An everywhere-unramified intermediate field of a totally ramified layer is the base field.
The conclusion is expressed as `⊥` over the layer base.

**Warning**: `htot` quantifies over *all* absolute values of `A`, including
`AbsoluteValue.trivial`, whose inertia subgroup is `⊥`
(`AbsoluteValue.inertiaSubgroup_eq_bot_of_not_isNontrivial`).  So `htot` alone forces
`(⊤ : Subgroup Gal(A/F)) = ⊥`, hence `A = ⊥` since `A / F` is finite Galois: the hypothesis is
satisfiable only when the conclusion already holds.  The intended statement, with total
ramification at a single place, is
`IntermediateField.eq_bot_of_isUnramifiedEverywhere_of_inertiaSubgroup_eq_top`
(`Iwasawalib/NumberTheory/ZpExtension/FiniteSubalgebraLinearDisjoint.lean`). -/
theorem intermediateField_eq_bot_of_totallyRamified_of_isUnramifiedEverywhere
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A : IntermediateField F L) [IsGalois F A]
    [FiniteDimensional F A]
    [NumberField.IsUnramifiedEverywhere F A]
    (htot : ∀ w : AbsoluteValue A ℝ, w.inertiaSubgroup F = ⊤) :
    A = ⊥ := by
  classical
  have hbot : ∀ w : AbsoluteValue A ℝ, w.inertiaSubgroup F = ⊥ :=
    fun w ↦ AbsoluteValue.inertiaSubgroup_eq_bot_of_isUnramifiedEverywhere F w
  have hgal : (⊤ : Subgroup (Gal(↥A / F))) = ⊥ := by
    let w : AbsoluteValue A ℝ := AbsoluteValue.trivial
    exact (htot w).symm.trans (hbot w)
  haveI : Subsingleton (Gal(↥A / F)) := by
    constructor
    intro σ τ
    have hσ : σ ∈ (⊥ : Subgroup (Gal(↥A / F))) := by
      rw [← hgal]
      exact Subgroup.mem_top _
    have hτ : τ ∈ (⊥ : Subgroup (Gal(↥A / F))) := by
      rw [← hgal]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_bot.mp hσ).trans (Subgroup.mem_bot.mp hτ).symm
  apply finrank_eq_one_iff.mp
  rw [← IsGalois.card_aut_eq_finrank F A]
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩

/-- Once the intermediate field is the base, the generic Mathlib bridge gives the corresponding
linear-disjointness conclusion. -/
theorem linearDisjoint_of_intermediateField_eq_bot
    {F E' : Type*} [Field F] [Field E'] [Algebra F E']
    (A B : IntermediateField F E')
  [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B]
  (hB : B = ⊥) : A.LinearDisjoint B := by
  rw [hB]
  exact IntermediateField.LinearDisjoint.bot_right A

end IntermediateField
