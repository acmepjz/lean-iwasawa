/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.ShiftLinf
public import Iwasawalib.NumberTheory.ZpExtension.Yn

@[expose] public section

/-!
# `Yₙ` does not change when the base is moved up the tower

`MvZpExtension.Linf_shift` and `MvZpExtension.Ln'_shift` say that moving the base field from
`K` to the layer `Kₑ` changes neither `L∞` nor the compositum layers `K∞Lₙ`, only their
indexing: `(H.shift e).Ln' n = H.Ln' (n + e)`.  This file draws the consequence for the
subgroups `Yₙ = Gal(L∞/K∞Lₙ)` of `MvZpExtension.Yn`:

`(H.shift e).Yₙ = Y_{n+e}` along `MvZpExtension.galLinfShiftContinuousMulEquiv`,

and the same for `MvZpExtension.YnIn` inside `X∞`.  This is the transport that blueprint node
`Xn-isom-qout-of-totally-ramified` needs in order to apply Step 1
(`MvZpExtension.xinfQuotientMulEquivOfPlace'`) at the shifted extension `H.shift n`, where
`K∞ / Kₙ` is totally ramified, and read the answer back over `K`.

## Transport implementation

The equality of intermediate fields is transported through their canonical algebra
isomorphism. In Lean 4.35, using equality elimination directly for the Galois-group
isomorphism caused kernel timeouts on these concrete fields; conjugation by
`IntermediateField.equivOfEq` avoids that reduction. The named map equalities below
keep downstream proofs independent of this implementation choice.

## Main results

* `MvZpExtension.mem_Yn_shift`: `(H.shift e).Yₙ = Y_{n+e}`.  Only the membership form is
  available: the `Subgroup.comap` form needs to *project* out of
  `MvZpExtension.galLinfShiftContinuousMulEquiv`, and the kernel cannot whnf that transport.
* `MvZpExtension.xinfShiftMulEquiv`, `MvZpExtension.xinfHom_xinfShiftMulEquiv`: the transport
  `X∞(K∞/Kₑ) ≃* X∞(K∞/K)` and its compatibility with `MvZpExtension.xinfHom`.
* `MvZpExtension.mem_YnIn_shift`, `MvZpExtension.YnIn_shift`: the same inside `X∞`.
-/

open IntermediateField NumberField

/-- The `MulEquiv` underlying a `ContinuousMulEquiv` has the same underlying function.  Stated
at abstract types on purpose: at the concrete Galois groups of this file the corresponding
`rfl` does not terminate. -/
theorem ContinuousMulEquiv.coe_toMulEquiv_apply {M N : Type*} [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] (g : M ≃ₜ* N) (y : M) :
    g.toMulEquiv y = g y := rfl

namespace IntermediateField

variable {A L : Type*} [Field A] [Field L] [Algebra A L]

/-- Transporting a "fixes every element of `S`" condition along
`IntermediateField.galContinuousMulEquivCongr`. -/
theorem forall_mem_imp_congr_galContinuousMulEquivCongr {E E' : IntermediateField A L}
    (h : E = E') (S : Set L) (σ : Gal(↥E/A)) :
    (∀ x : ↥E, (x : L) ∈ S → σ x = x) ↔
      (∀ y : ↥E', (y : L) ∈ S → (galContinuousMulEquivCongr h σ) y = y) := by
  subst h
  rfl

end IntermediateField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf) (e : ℕ)

/-! ### `Yₙ` inside `Gal(L∞/K∞)` -/

/-- `MvZpExtension.galLinfShiftContinuousMulEquiv` is
`IntermediateField.galContinuousMulEquivCongr` at `MvZpExtension.Linf_shift`.  This equation
between *maps* is `rfl`; the corresponding equation between their values at an element is not
provable by `rfl` in any feasible time. -/
theorem galLinfShiftContinuousMulEquiv_eq :
    H.galLinfShiftContinuousMulEquiv e =
      IntermediateField.galContinuousMulEquivCongr (H.Linf_shift e) := rfl

theorem galLinfShiftContinuousMulEquiv_apply (σ : Gal(↥(H.shift e).Linf/Kinf)) :
    H.galLinfShiftContinuousMulEquiv e σ =
      IntermediateField.galContinuousMulEquivCongr (H.Linf_shift e) σ := by
  rw [H.galLinfShiftContinuousMulEquiv_eq e]

set_option maxHeartbeats 1000000 in
/-- **`Yₙ` of the shifted extension is `Y_{n+e}`**, in terms of
`IntermediateField.galContinuousMulEquivCongr`. -/
theorem mem_Yn_shift_congr (n : ℕ) (σ : Gal(↥(H.shift e).Linf/Kinf)) :
    σ ∈ (H.shift e).Yn n ↔
      IntermediateField.galContinuousMulEquivCongr (H.Linf_shift e) σ ∈ H.Yn (n + e) := by
  rw [mem_Yn_iff, mem_Yn_iff]
  have key := IntermediateField.forall_mem_imp_congr_galContinuousMulEquivCongr
    (H.Linf_shift e) (H.Ln' (n + e) : Set (SeparableClosure Kinf)) σ
  have hmem1 : ∀ x : ↥(H.shift e).Linf, x ∈ (H.shift e).Ln'In n ↔
      (x : SeparableClosure Kinf) ∈ (H.Ln' (n + e) : Set (SeparableClosure Kinf)) := by
    intro x
    rw [(H.shift e).mem_Ln'In n x, H.Ln'_shift e n]
    exact Iff.rfl
  have hmem2 : ∀ y : ↥H.Linf, y ∈ H.Ln'In (n + e) ↔
      (y : SeparableClosure Kinf) ∈ (H.Ln' (n + e) : Set (SeparableClosure Kinf)) :=
    fun y ↦ H.mem_Ln'In (n + e) y
  constructor
  · intro hσ y hy
    exact key.1 (fun x hx ↦ hσ x ((hmem1 x).2 hx)) y ((hmem2 y).1 hy)
  · intro hσ x hx
    exact key.2 (fun y hy ↦ hσ y ((hmem2 y).2 hy)) x ((hmem1 x).1 hx)

/-- **`Yₙ` of the shifted extension is `Y_{n+e}`**, along
`MvZpExtension.galLinfShiftContinuousMulEquiv`. -/
theorem mem_Yn_shift (n : ℕ) (σ : Gal(↥(H.shift e).Linf/Kinf)) :
    σ ∈ (H.shift e).Yn n ↔ H.galLinfShiftContinuousMulEquiv e σ ∈ H.Yn (n + e) :=
  (H.mem_Yn_shift_congr e n σ).trans
    (iff_of_eq (congrArg (· ∈ H.Yn (n + e))
      (H.galLinfShiftContinuousMulEquiv_apply e σ).symm))

/-! ### `Yₙ` inside `X∞` -/

/-- **`X∞` does not change when the base is moved up the tower**, as abstract groups.  This is
`MvZpExtension.xinfShiftContinuousMulEquiv` (`MvZpExtension.xinfShiftMulEquiv_eq`), written out
so that its value at an element can be computed without unfolding a transport along `▸`. -/
noncomputable def xinfShiftMulEquiv : ↥(H.shift e).Xinf ≃* ↥H.Xinf :=
  ((H.shift e).xinfMulEquiv.trans (H.galLinfShiftContinuousMulEquiv e).toMulEquiv).trans
    H.xinfMulEquiv.symm

/-- `MvZpExtension.xinfShiftMulEquiv` is `MvZpExtension.xinfShiftContinuousMulEquiv`. -/
theorem xinfShiftMulEquiv_eq :
    H.xinfShiftMulEquiv e = (H.xinfShiftContinuousMulEquiv e).toMulEquiv := rfl

/-- **The transport of `X∞` is compatible with `X∞ ≅ Gal(L∞/K∞)`.** -/
theorem xinfHom_xinfShiftMulEquiv (x : ↥(H.shift e).Xinf) :
    H.xinfHom (H.xinfShiftMulEquiv e x) =
      H.galLinfShiftContinuousMulEquiv e ((H.shift e).xinfHom x) := by
  rw [xinfShiftMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← H.xinfMulEquiv_apply, MulEquiv.apply_symm_apply, (H.shift e).xinfMulEquiv_apply,
    ContinuousMulEquiv.coe_toMulEquiv_apply]

/-- **`Yₙ ∩ X∞` of the shifted extension is `Y_{n+e} ∩ X∞`**, membership form. -/
theorem mem_YnIn_shift (n : ℕ) (x : ↥(H.shift e).Xinf) :
    x ∈ (H.shift e).YnIn n ↔ H.xinfShiftMulEquiv e x ∈ H.YnIn (n + e) := by
  rw [mem_YnIn_iff, mem_YnIn_iff, H.mem_Yn_shift e n ((H.shift e).xinfHom x),
    H.xinfHom_xinfShiftMulEquiv e x]

/-- **`Yₙ ∩ X∞` of the shifted extension is `Y_{n+e} ∩ X∞`.** -/
theorem YnIn_shift (n : ℕ) :
    (H.shift e).YnIn n = (H.YnIn (n + e)).comap (H.xinfShiftMulEquiv e).toMonoidHom :=
  Subgroup.ext fun x ↦ H.mem_YnIn_shift e n x

end MvZpExtension
