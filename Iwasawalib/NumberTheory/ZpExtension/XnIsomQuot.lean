/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.ShiftStepOne
public import Iwasawalib.NumberTheory.ZpExtension.YnShift

@[expose] public section

/-!
# `Xₙ ≅ X∞ / Yₙ ≅ G_n / (I_w Yₙ)`: Step 1 of `Xn-isom-qout`, read over `K`

`MvZpExtension.xinfQuotientMulEquivOfPlace'` proves Step 1 of blueprint node
`Xn-isom-qout-of-totally-ramified` over the base field of the `ℤₚ`-extension it is applied to,
and total ramification is only available after moving the base up the tower
(`MvZpExtension.exists_shift_totally_ramified`).  This file applies Step 1 at `H.shift n` with
`Y = Yₙ` and reads the answer back over `K`, using that `X∞` and `Yₙ` do not change
(`MvZpExtension.xinfShiftMulEquiv`, `MvZpExtension.YnIn_shift`):

`X∞ / Yₙ ≅ G_n / (I_w Yₙ)`,  `G_n = Gal(L∞/Kₙ)`.

Combined with `MvZpExtension.xinfInQuotientYnMulEquiv` (`X∞ / Yₙ ≅ Xₙ`, the field-theoretic
half, already available) this is `Xₙ ≅ G_n / (I_w Yₙ)`.

Two hypotheses stay parameters, because both are class field theory and neither is available in
the repository: that the place `w` lies over a place at which `K∞ / Kₙ` is totally ramified
(supplied by `MvZpExtension.exists_shift_totally_ramified` once the ramified family is known),
and `T X∞ ⊆ Yₙ`, i.e. that `K∞Lₙ / Kₙ` is abelian.

## Main definitions

* `MvZpExtension.YnInShift`: `Yₙ`, as a subgroup of `G_n = Gal(L∞/Kₙ)`.
* `MvZpExtension.xinfShiftQuotientYnMulEquiv`: `X∞(K∞/Kₙ) / Yₙ ≅ X∞(K∞/K) / Yₙ`.
* `MvZpExtension.xinfQuotientYnMulEquivQuotientInertia`: **Step 1 over `K`**.
-/

open IntermediateField NumberField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- `Yₙ ∩ X∞` is normal in `X∞`: it is the preimage of the normal subgroup `Yₙ`. -/
instance normal_YnIn (n : ℕ) : (H.YnIn n).Normal := Subgroup.normal_comap _

/-! ### `Yₙ` as a subgroup of `G_n` -/

/-- `Yₙ = Gal(L∞/K∞Lₙ)`, as a subgroup of `G_n = Gal(L∞/Kₙ)`.  This is the `Y` that Step 1 is
applied to at `H.shift n`. -/
noncomputable def YnInShift (n : ℕ) : Subgroup (H.shift n).GG :=
  ((H.shift n).YnIn 0).map (H.shift n).Xinf.subtype

theorem YnInShift_le (n : ℕ) : H.YnInShift n ≤ (H.shift n).Xinf :=
  Subgroup.map_subtype_le _

theorem subgroupOf_YnInShift (n : ℕ) :
    (H.YnInShift n).subgroupOf (H.shift n).Xinf = (H.shift n).YnIn 0 :=
  Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _

/-! ### `Yₙ` is the same before and after the shift -/

theorem map_YnIn_xinfShiftMulEquiv (n : ℕ) :
    Subgroup.map (H.xinfShiftMulEquiv n).toMonoidHom ((H.shift n).YnIn 0) = H.YnIn n := by
  rw [H.YnIn_shift n 0, Subgroup.map_comap_eq_self_of_surjective
    (H.xinfShiftMulEquiv n).surjective, zero_add]

/-- **`X∞(K∞/Kₙ) / Yₙ ≅ X∞(K∞/K) / Yₙ`**: the two readings of `X∞ / Yₙ`, before and after
moving the base to `Kₙ`, agree. -/
noncomputable def xinfShiftQuotientYnMulEquiv (n : ℕ) :
    (↥(H.shift n).Xinf ⧸ (H.shift n).YnIn 0) ≃* (↥H.Xinf ⧸ H.YnIn n) :=
  QuotientGroup.congr _ _ (H.xinfShiftMulEquiv n) (H.map_YnIn_xinfShiftMulEquiv n)


end MvZpExtension

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-! ### Step 1 of `Xn-isom-qout-of-totally-ramified`, over `K` -/

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 1, read over `K`.**  Let `w` be a
place of `L∞` lying over a place of `K∞` at which `K∞ / Kₙ` is totally ramified, and suppose
`K∞Lₙ / Kₙ` is abelian, in the form `T X∞ ⊆ Yₙ`.  Then

`X∞ / Yₙ ≅ G_n / (I_w Yₙ)`, `G_n = Gal(L∞/Kₙ)`,

with `X∞ = Gal(L∞/K∞)` read as a subgroup of `Gal(L∞/K)`.  Composed with
`MvZpExtension.xinfInQuotientYnMulEquiv` this identifies `Xₙ = Gal(K∞Lₙ/K∞)` with
`G_n / (I_w Yₙ)`. -/
noncomputable def xinfQuotientYnMulEquivQuotientInertia (n : ℕ)
    (γ : (H.shift n).GG ⧸ (H.shift n).Xinf)
    (hγ : Dense (Subgroup.zpowers γ : Set ((H.shift n).GG ⧸ (H.shift n).Xinf)))
    (w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ)
    (hram : ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤)
    (hTY : Subgroup.gammaSubOneG (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ ≤
      H.YnInShift n) :
    letI : (H.YnInShift n).Normal :=
      Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
        (H.shift n).isClosed_Xinf hγ hTY
    letI : ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔ H.YnInShift n).Normal :=
      Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
        (H.shift n).isClosed_Xinf hγ (le_trans hTY (le_sup_right : H.YnInShift n ≤ _))
    (↥H.Xinf ⧸ H.YnIn n) ≃*
      ((H.shift n).GG ⧸ ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔ H.YnInShift n)) :=
  letI : (H.YnInShift n).Normal :=
    Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
      (H.shift n).isClosed_Xinf hγ hTY
  letI : ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔ H.YnInShift n).Normal :=
    Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
      (H.shift n).isClosed_Xinf hγ (le_trans hTY (le_sup_right : H.YnInShift n ≤ _))
  letI : ((H.YnInShift n).subgroupOf (H.shift n).Xinf).Normal := Subgroup.normal_comap _
  ((H.xinfShiftQuotientYnMulEquiv n).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (H.subgroupOf_YnInShift n).symm)).trans
    ((H.shift n).xinfQuotientMulEquivOfPlace' γ hγ w hram (H.YnInShift n) (H.YnInShift_le n) hTY)

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 1, in terms of `Xₙ`.**  Under the
same hypotheses, `Xₙ = Gal(K∞Lₙ/K∞) ≅ G_n / (I_w Yₙ)`.  This is
`MvZpExtension.xinfQuotientYnMulEquivQuotientInertia` composed with the field-theoretic
identification `MvZpExtension.xinfInQuotientYnMulEquiv` of `X∞ / Yₙ` with `Xₙ`. -/
noncomputable def xnMulEquivQuotientInertia (n : ℕ)
    (γ : (H.shift n).GG ⧸ (H.shift n).Xinf)
    (hγ : Dense (Subgroup.zpowers γ : Set ((H.shift n).GG ⧸ (H.shift n).Xinf)))
    (w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ)
    (hram : ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤)
    (hTY : Subgroup.gammaSubOneG (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ ≤
      H.YnInShift n) :
    letI : (H.YnInShift n).Normal :=
      Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
        (H.shift n).isClosed_Xinf hγ hTY
    letI : ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔ H.YnInShift n).Normal :=
      Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
        (H.shift n).isClosed_Xinf hγ (le_trans hTY (le_sup_right : H.YnInShift n ≤ _))
    Gal(↥(H.Ln' n)/Kinf) ≃*
      ((H.shift n).GG ⧸ ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔
        H.YnInShift n)) :=
  letI : ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔ H.YnInShift n).Normal :=
    Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
      (H.shift n).isClosed_Xinf hγ (le_trans hTY (le_sup_right : H.YnInShift n ≤ _))
  (H.xinfInQuotientYnMulEquiv n).symm.trans
    (H.xinfQuotientYnMulEquivQuotientInertia n γ hγ w hram hTY)

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
/-- **`#Xₙ = #(G_n / I_w Yₙ)`.**  Together with
`MvZpExtension.card_quotient_YnSubmodule` this is the first of the two factors of the
hypothesis `hcard` of `MvZpExtension.exists_multiplicity_classNumber_of_card_eq`; the second,
`#Xₙ = p ^ ord_p(h_{Kₙ})`, is blueprint node `Xn-isom-An` and is class field theory. -/
theorem card_gal_Ln'_eq (n : ℕ)
    (γ : (H.shift n).GG ⧸ (H.shift n).Xinf)
    (hγ : Dense (Subgroup.zpowers γ : Set ((H.shift n).GG ⧸ (H.shift n).Xinf)))
    (w : AbsoluteValue ↥((H.shift n).Linf.restrictScalars ↥(H.Kn n)) ℝ)
    (hram : ((H.shift n).placeBelow w).inertiaSubgroup ↥(H.Kn n) = ⊤)
    (hTY : Subgroup.gammaSubOneG (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ ≤
      H.YnInShift n) :
    letI : (H.YnInShift n).Normal :=
      Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
        (H.shift n).isClosed_Xinf hγ hTY
    letI : ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔ H.YnInShift n).Normal :=
      Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
        (H.shift n).isClosed_Xinf hγ (le_trans hTY (le_sup_right : H.YnInShift n ≤ _))
    Nat.card Gal(↥(H.Ln' n)/Kinf) =
      Nat.card ((H.shift n).GG ⧸ ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔
        H.YnInShift n)) :=
  letI : ((w.inertiaSubgroup ↥(H.Kn n) : Subgroup (H.shift n).GG) ⊔ H.YnInShift n).Normal :=
    Subgroup.normal_of_gammaSubOneG_le (H.shift n).Xinf (H.shift n).mul_comm_Xinf' γ
      (H.shift n).isClosed_Xinf hγ (le_trans hTY (le_sup_right : H.YnInShift n ≤ _))
  Nat.card_congr (H.xnMulEquivQuotientInertia n γ hγ w hram hTY).toEquiv

end MvZpExtension
