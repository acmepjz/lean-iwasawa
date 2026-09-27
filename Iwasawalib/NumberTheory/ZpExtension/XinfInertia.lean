/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.GaloisGroupProP
public import Iwasawalib.NumberTheory.ZpExtension.InertiaQuotient

@[expose] public section

/-!
# `Γ` is topologically cyclic, and Step 1 of Washington's Lemma 13.15 for `X∞` and `G`

Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 1, reads
`X₀ = G/H = XI/YI ≅ X/(X ∩ YI) = X/Y`.  The group theory is
`Subgroup.mulEquivQuotientOfInertia'` (in
`Iwasawalib.NumberTheory.ZpExtension.InertiaQuotient`), whose hypotheses are: `X` abelian
normal and closed, a topological generator `γ` of `Γ = G ⧸ X`, a subgroup `Y ≤ X` containing
`T X`, and an inertia subgroup `I` with `I ∩ X = 1` and `G = X I`.

This file discharges everything about `X = X∞` and `G = Gal(L∞/K)`:

* `MvZpExtension.mul_comm_Xinf'` (abelian) and `MvZpExtension.isClosed_Xinf` (closed) are
  already available;
* `MvZpExtension.gammaContinuousMulEquiv` identifies `Γ = G ⧸ X∞` with `Gal(K∞/K)` *as a
  topological group* — the map `MvZpExtension.toGamma` is continuous, and a continuous
  bijection from a compact space to a Hausdorff space is a homeomorphism;
* hence `MvZpExtension.exists_dense_zpowers`: in the `ℤₚ`-case (`Unique ι`) the group `Γ` has
  a topological generator, transported from `EquivMvZp.topologicalGenerator`.

What is *not* here is the inertia subgroup `I` itself: in
`MvZpExtension.xinfQuotientMulEquivOfInertia` it is a hypothesis, with the two properties it is
supposed to have.  It is produced downstream, in
`Iwasawalib/NumberTheory/ZpExtension/XinfStepOne.lean`: there `I = I_w(L∞/K)` is the inertia
subgroup of a place `w` of `L∞`, the property `I ∩ X∞ = 1` is
`MvZpExtension.inertiaSubgroup_inf_Xinf` (`L∞ / K∞` is unramified), and `G = X∞ I` is
`MvZpExtension.exists_mem_Xinf_mul_mem_inertiaSubgroup`, under total ramification of `K∞ / K`
at the place below `w`.  Step 1 with `I` produced is `MvZpExtension.xinfQuotientMulEquivOfPlace`
and `MvZpExtension.xinfQuotientMulEquivOfPlace'`.  Total ramification holds over a suitable
layer `Kₑ` at a given finite family of ramified places by `MvZpExtension.exists_totally_ramified`,
which uses that inertia subgroups are closed (`AbsoluteValue.isClosed_inertiaSubgroup`); `Kₑ` is
made the base by `MvZpExtension.shift`, as in
`Iwasawalib/NumberTheory/ZpExtension/ShiftStepOne.lean`.

## Main results

* `MvZpExtension.continuous_toGamma`, `MvZpExtension.gammaContinuousMulEquiv`.
* `MvZpExtension.exists_dense_zpowers`.
* `MvZpExtension.xinfQuotientMulEquivOfInertia`: Step 1, for `X∞` and `G`.
-/

open IntermediateField Topology

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-! ### `Γ = G ⧸ X∞` is `Gal(K∞/K)` topologically -/

set_option linter.unusedSectionVars false in
/-- The restriction map `G → Γ` is continuous. -/
theorem continuous_toGamma : Continuous H.toGamma :=
  (H.kinfInEquiv.continuous_autCongr).comp
    (InfiniteGalois.restrictNormalHom_continuous H.KinfIn)

set_option linter.unusedSectionVars false in
/-- `MvZpExtension.gammaMulEquiv` is induced by `MvZpExtension.toGamma`. -/
theorem gammaMulEquiv_mk (g : H.GG) : H.gammaMulEquiv (QuotientGroup.mk g) = H.toGamma g := rfl

set_option linter.unusedSectionVars false in
/-- `MvZpExtension.gammaMulEquiv` is continuous. -/
theorem continuous_gammaMulEquiv : Continuous H.gammaMulEquiv := by
  have hq : IsQuotientMap (QuotientGroup.mk : H.GG → H.GG ⧸ H.Xinf) :=
    (QuotientGroup.isOpenMap_coe (N := H.Xinf)).isQuotientMap
      continuous_quot_mk Quot.mk_surjective
  rw [hq.continuous_iff]
  exact H.continuous_toGamma

/-- **`Γ = G ⧸ X∞ ≅ Gal(K∞/K)` as topological groups.** -/
noncomputable def gammaContinuousMulEquiv : (H.GG ⧸ H.Xinf) ≃ₜ* Gal(Kinf/K) :=
  letI h : (H.GG ⧸ H.Xinf) ≃ₜ Gal(Kinf/K) :=
    H.continuous_gammaMulEquiv.homeoOfEquivCompactToT2 (f := H.gammaMulEquiv.toEquiv)
  { toMulEquiv := H.gammaMulEquiv
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

/-- **In the `ℤₚ`-case, `Γ = G ⧸ X∞` has a topological generator.**  This is the hypothesis
`hγ` of `Subgroup.commutator_eq_gammaSubOneG` and
`Subgroup.mulEquivQuotientOfInertia'`. -/
theorem exists_dense_zpowers [Unique ι] :
    ∃ γ : H.GG ⧸ H.Xinf, Dense (Subgroup.zpowers γ : Set (H.GG ⧸ H.Xinf)) := by
  set e := H.gammaContinuousMulEquiv
  refine ⟨e.symm H.topologicalGenerator, ?_⟩
  have hd : Dense (Subgroup.zpowers H.topologicalGenerator : Set Gal(Kinf/K)) := by
    have h := H.topologicalGenerator_spec
    rw [← Subgroup.zpowers_eq_closure] at h
    exact dense_iff_closure_eq.2 h
  have himg : ((Subgroup.zpowers (e.symm H.topologicalGenerator)) : Set (H.GG ⧸ H.Xinf))
      = e.symm '' (Subgroup.zpowers H.topologicalGenerator : Set Gal(Kinf/K)) := by
    have hmap : (Subgroup.zpowers H.topologicalGenerator).map
        ((e.symm : (Gal(Kinf/K) ≃* (H.GG ⧸ H.Xinf))) : Gal(Kinf/K) →* (H.GG ⧸ H.Xinf))
        = Subgroup.zpowers (e.symm H.topologicalGenerator) := MonoidHom.map_zpowers _ _
    rw [← hmap, Subgroup.coe_map]
    rfl
  rw [himg]
  refine dense_iff_closure_eq.2 ?_
  have hcoe : (⇑e.symm : Gal(Kinf/K) → (H.GG ⧸ H.Xinf)) = ⇑e.toHomeomorph.symm := rfl
  rw [hcoe, ← e.toHomeomorph.symm.image_closure, dense_iff_closure_eq.1 hd]
  exact Set.image_univ_of_surjective e.toHomeomorph.symm.surjective

/-! ### Step 1 of Washington's Lemma 13.15 -/

/-- Commutativity of `X∞`, in the shape the `Subgroup` lemmas of
`Iwasawalib.NumberTheory.ZpExtension.CommutatorEq` expect. -/
theorem mul_comm_Xinf' : ∀ a ∈ H.Xinf, ∀ b ∈ H.Xinf, a * b = b * a := H.mul_comm_Xinf

/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 1, for `X∞` and `G`.**  Given a
subgroup `I ⊆ G` meeting `X∞` trivially with `G = X∞ I` — the inertia subgroup of a place,
once `K∞ / K` is totally ramified there — and a subgroup `Y ≤ X∞` containing `T X∞`, one has
`X∞ / Y ≅ G / IY`. -/
noncomputable def xinfQuotientMulEquivOfInertia (γ : H.GG ⧸ H.Xinf)
    (hγ : Dense (Subgroup.zpowers γ : Set (H.GG ⧸ H.Xinf)))
    (I Y : Subgroup H.GG) (hYX : Y ≤ H.Xinf)
    (hTY : Subgroup.gammaSubOneG H.Xinf H.mul_comm_Xinf' γ ≤ Y)
    (hIX : ∀ g : H.GG, g ∈ I → g ∈ H.Xinf → g = 1)
    (hG : ∀ g : H.GG, ∃ x ∈ H.Xinf, ∃ i ∈ I, g = x * i) :
    letI : Y.Normal := Subgroup.normal_of_gammaSubOneG_le H.Xinf H.mul_comm_Xinf' γ
      H.isClosed_Xinf hγ hTY
    letI : (I ⊔ Y).Normal := Subgroup.normal_of_gammaSubOneG_le H.Xinf H.mul_comm_Xinf' γ
      H.isClosed_Xinf hγ (le_trans hTY (le_sup_right : Y ≤ I ⊔ Y))
    (H.Xinf ⧸ Y.subgroupOf H.Xinf) ≃* (H.GG ⧸ (I ⊔ Y)) :=
  Subgroup.mulEquivQuotientOfInertia' H.Xinf H.mul_comm_Xinf' γ H.isClosed_Xinf hγ I Y
    hYX hTY hIX hG

/-- The commutator subgroup of `G` is `T X∞`, blueprint node `commutator-eq`, for `X∞`. -/
theorem commutator_GG_eq (γ : H.GG ⧸ H.Xinf)
    (hγ : Dense (Subgroup.zpowers γ : Set (H.GG ⧸ H.Xinf))) :
    commutator H.GG = Subgroup.gammaSubOneG H.Xinf H.mul_comm_Xinf' γ :=
  Subgroup.commutator_eq_gammaSubOneG H.Xinf H.mul_comm_Xinf' γ H.isClosed_Xinf hγ

end MvZpExtension
