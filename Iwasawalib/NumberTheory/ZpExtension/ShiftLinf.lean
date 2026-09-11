/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.LnTower
public import Iwasawalib.NumberTheory.ZpExtension.Shift
public import Iwasawalib.NumberTheory.ZpExtension.XinfInvLimit

@[expose] public section

/-!
# `L∞` and `X∞` do not change when the base is moved up the tower

Let `K∞ / K` be a `ℤₚᵈ`-extension of number fields and let `H.shift e` be the same extension
read as a `ℤₚᵈ`-extension of the layer `Kₑ` (`MvZpExtension.shift`).  Its layers are the later
layers of the original tower (`MvZpExtension.restrictScalars_Kn_shift`), so its maximal
unramified abelian `p`-extensions are the later `Lₙ` and its `L∞` is literally the *same*
intermediate field of `SeparableClosure K∞` over `K∞`.  Hence `X∞ = Gal(L∞/K∞)` is the same
group as well.

The identification of the `Lₙ` is the point where the two base fields `↥((H.shift e).Kₙ)` and
`↥(Kₙ₊ₑ)` — equal as subsets of `K∞`, but *different types* carrying different
`Algebra`/`IsScalarTower` instances — have to be compared.  It is done with
`IntermediateField.adjoin_le_lift_maximalGaloisSExtension_of_ringHom`, applied in both
directions with the identity-on-carriers ring isomorphism `MvZpExtension.shiftKnRingHom`.  No
`rfl` between the two `algebraMap`s is ever attempted: that diverges in the kernel.

## Main results

* `MvZpExtension.coe_Ln_shift`: `(H.shift e).Lₙ = L_{n+e}` as subsets of the separable closure.
* `MvZpExtension.Linf_shift`: `(H.shift e).L∞ = L∞`.
* `MvZpExtension.xinfShiftContinuousMulEquiv`: `X∞(K∞/Kₑ) ≃ₜ* X∞(K∞/K)`.
-/

open IntermediateField NumberField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf) (e : ℕ)

/-! ### The layers of the shifted extension, as fields -/

/-- The identity on carriers, as a ring homomorphism `↥((H.shift e).Kₙ) →+* ↥(K_{n+e})`. -/
noncomputable def shiftKnRingHom (n : ℕ) : ↥((H.shift e).Kn n) →+* ↥(H.Kn (n + e)) :=
  IntermediateField.ringHomOfMemImp ((H.shift e).Kn n) (H.Kn (n + e))
    fun x hx ↦ (mem_Kn_shift_iff (H := H) (e := e) n x).1 hx

/-- The identity on carriers, as a ring homomorphism `↥(K_{n+e}) →+* ↥((H.shift e).Kₙ)`. -/
noncomputable def shiftKnRingHom' (n : ℕ) : ↥(H.Kn (n + e)) →+* ↥((H.shift e).Kn n) :=
  IntermediateField.ringHomOfMemImp (H.Kn (n + e)) ((H.shift e).Kn n)
    fun x hx ↦ (mem_Kn_shift_iff (H := H) (e := e) n x).2 hx

omit [NumberField K] in
theorem algebraMap_shiftKnRingHom (n : ℕ) (x : ↥((H.shift e).Kn n)) :
    algebraMap ↥((H.shift e).Kn n) (SeparableClosure Kinf) x =
      algebraMap ↥(H.Kn (n + e)) (SeparableClosure Kinf) (H.shiftKnRingHom e n x) :=
  IntermediateField.algebraMap_ringHomOfMemImp _ _ _ _ x

omit [NumberField K] in
theorem algebraMap_shiftKnRingHom' (n : ℕ) (x : ↥(H.Kn (n + e))) :
    algebraMap ↥(H.Kn (n + e)) (SeparableClosure Kinf) x =
      algebraMap ↥((H.shift e).Kn n) (SeparableClosure Kinf) (H.shiftKnRingHom' e n x) :=
  IntermediateField.algebraMap_ringHomOfMemImp _ _ _ _ x

/-- **The `Lₙ` of the shifted extension are the later `Lₙ`.** -/
theorem coe_Ln_shift (n : ℕ) :
    ((H.shift e).Ln n : Set (SeparableClosure Kinf)) =
      (H.Ln (n + e) : Set (SeparableClosure Kinf)) := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · refine IntermediateField.adjoin_le_lift_maximalGaloisSExtension_of_ringHom
      (H.shiftKnRingHom e n) (H.algebraMap_shiftKnRingHom e n) ((H.shift e).Ln n) ?_
    exact IntermediateField.subset_adjoin _ _ hx
  · refine IntermediateField.adjoin_le_lift_maximalGaloisSExtension_of_ringHom
      (H.shiftKnRingHom' e n) (H.algebraMap_shiftKnRingHom' e n) (H.Ln (n + e)) ?_
    exact IntermediateField.subset_adjoin _ _ hx

/-! ### `L∞` and `X∞` -/

/-- The compositum `K∞ Lₙ` of the shifted extension is `K∞ L_{n+e}`. -/
theorem Ln'_shift (n : ℕ) : (H.shift e).Ln' n = H.Ln' (n + e) := by
  rw [Ln', Ln', H.coe_Ln_shift e n]

/-- **`L∞` does not change when the base is moved up the tower.** -/
theorem Linf_shift : (H.shift e).Linf = H.Linf := by
  refine le_antisymm (iSup_le fun n ↦ ?_) (iSup_le fun n ↦ ?_)
  · rw [H.Ln'_shift e n]
    exact H.Ln'_le_Linf (n + e)
  · exact le_trans (H.monotone_Ln' (Nat.le_add_right n e))
      (le_trans (le_of_eq (H.Ln'_shift e n).symm) ((H.shift e).Ln'_le_Linf n))

/-- `Gal(L∞/K∞)` computed from the shifted extension is `Gal(L∞/K∞)`. -/
noncomputable def galLinfShiftContinuousMulEquiv :
    Gal(↥(H.shift e).Linf/Kinf) ≃ₜ* Gal(↥H.Linf/Kinf) :=
  IntermediateField.galContinuousMulEquivCongr (H.Linf_shift e)

/-- **`X∞` does not change when the base is moved up the tower.** -/
noncomputable def xinfShiftContinuousMulEquiv :
    ↥(H.shift e).Xinf ≃ₜ* ↥H.Xinf :=
  (((H.shift e).xinfContinuousMulEquiv.trans (galLinfShiftContinuousMulEquiv H e)).trans
    H.xinfContinuousMulEquiv.symm)

end MvZpExtension
