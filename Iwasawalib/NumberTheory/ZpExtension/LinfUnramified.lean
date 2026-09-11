/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.AbsoluteValue.InfiniteInertia
public import Iwasawalib.NumberTheory.ZpExtension.XinfInvLimit

@[expose] public section

/-!
# `L∞ / K∞` is unramified

`L∞ = ⋃ₙ K∞Lₙ` is a union of extensions of `K∞` which are unramified everywhere
(`MvZpExtension.isUnramifiedEverywhere_Ln'`), so every place of `L∞` has trivial inertia over
`K∞`.  This is the half of the input to Step 1 of Washington's Lemma 13.15 that says the
inertia subgroup `I` of a place of `L∞` meets `X∞ = Gal(L∞/K∞)` trivially.

## Main results

* `MvZpExtension.inertiaSubgroup_Linf_eq_bot`: `I_w(L∞/K∞) = 1`.
* `MvZpExtension.inertiaSubgroup_KinfIn_eq_bot`: the same statement for `L∞` viewed as an
  extension of `K` (`MvZpExtension.GG` lives there) and `K∞` viewed as the intermediate field
  `MvZpExtension.KinfIn`.
-/

open IntermediateField

/-- The inverse of `IntermediateField.botEquiv`, read as an equality in the big field.

TODO: go mathlib. -/
theorem IntermediateField.algebraMap_botEquiv_apply {F E : Type*} [Field F] [Field E]
    [Algebra F E] (y : (⊥ : IntermediateField F E)) :
    algebraMap F E (IntermediateField.botEquiv F E y) = (y : E) := by
  have h := IntermediateField.botEquiv_symm (F := F) (E := E)
    (IntermediateField.botEquiv F E y)
  rw [AlgEquiv.symm_apply_apply] at h
  exact congrArg Subtype.val h.symm

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

instance isUnramifiedEverywhere_Ln'In (n : ℕ) :
    NumberField.IsUnramifiedEverywhere Kinf ↥(H.Ln'In n) :=
  NumberField.IsUnramifiedEverywhere.of_algEquiv
    (IntermediateField.restrict_algEquiv (H.Ln'_le_Linf n))

/-- **`L∞ / K∞` is unramified.**  Every place of `L∞` has trivial inertia subgroup in
`Gal(L∞/K∞)`. -/
theorem inertiaSubgroup_Linf_eq_bot (w : AbsoluteValue ↥H.Linf ℝ) :
    w.inertiaSubgroup Kinf = ⊥ :=
  AbsoluteValue.inertiaSubgroup_eq_bot_of_iSup_eq_top H.Ln'In H.iSup_Ln'In w fun n ↦
    AbsoluteValue.inertiaSubgroup_eq_bot_of_isUnramifiedEverywhere Kinf _

/-! ### The same, inside `L∞ / K` -/

/-- The bridge `K∞ ≅ K∞In` is compatible with the bridge `L∞ ≅ L∞` across `restrictScalars`. -/
theorem algebraMap_comp_kinfInEquiv :
    (algebraMap Kinf ↥H.Linf).comp (H.kinfInEquiv : ↥H.KinfIn →+* Kinf) =
      RingHom.comp (restrictScalarsAlgEquiv K H.Linf : ↥(H.Linf.restrictScalars K) ≃+* ↥H.Linf)
        (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)) :=
  RingHom.ext fun y ↦ IntermediateField.algebraMap_botEquiv_apply (F := Kinf) (E := ↥H.Linf) y

/-- **`L∞ / K∞` is unramified**, stated for `L∞` as an extension of `K` and `K∞` as the
intermediate field `MvZpExtension.KinfIn`.  This is the form Step 1 of Washington's Lemma
13.15 consumes. -/
theorem inertiaSubgroup_KinfIn_eq_bot (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ) :
    w.inertiaSubgroup ↥H.KinfIn = ⊥ := by
  let g : ↥(H.Linf.restrictScalars K) ≃+* ↥H.Linf :=
    (restrictScalarsAlgEquiv K H.Linf : ↥(H.Linf.restrictScalars K) ≃+* ↥H.Linf)
  let v : AbsoluteValue ↥H.Linf ℝ := w.comp (f := (g.symm : ↥H.Linf →+* _)) g.symm.injective
  have hvw : v.comp (f := (g : ↥(H.Linf.restrictScalars K) →+* ↥H.Linf)) g.injective = w :=
    AbsoluteValue.ext fun x ↦ congrArg w (g.symm_apply_apply x)
  rw [← AbsoluteValue.isUnramified_iff_inertiaSubgroup_eq_bot, ← hvw,
    v.isUnramified_comp_ringEquiv_iff (f := (H.kinfInEquiv : ↥H.KinfIn →+* Kinf)) (g := g)
      H.kinfInEquiv.surjective H.algebraMap_comp_kinfInEquiv,
    AbsoluteValue.isUnramified_iff_inertiaSubgroup_eq_bot]
  exact H.inertiaSubgroup_Linf_eq_bot v

end MvZpExtension
