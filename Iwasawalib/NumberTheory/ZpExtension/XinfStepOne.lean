/-
Copyright (c) 2026 Iwasawalib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iwasawalib.NumberTheory.ZpExtension.LinfUnramified
public import Iwasawalib.NumberTheory.ZpExtension.TotallyRamifiedLayer
public import Iwasawalib.NumberTheory.ZpExtension.XinfInertia

@[expose] public section

/-!
# The inertia subgroup `I` of Step 1 of Washington's Lemma 13.15

`MvZpExtension.xinfQuotientMulEquivOfInertia` states Step 1 of blueprint node
`Xn-isom-qout-of-totally-ramified` with the inertia subgroup `I ⊆ G = Gal(L∞/K)` left as a
hypothesis, carrying the two properties `I ∩ X∞ = 1` and `G = X∞ I`.  This file produces `I`:
it is the honest inertia subgroup `I_w(L∞/K)` of a place `w` of `L∞`, and the two properties
are discharged from

* `MvZpExtension.inertiaSubgroup_KinfIn_eq_bot` (`L∞ / K∞` is unramified), and
* total ramification of `K∞ / K` at the place below `w`, which for a `ℤₚ`-extension holds
  above some layer by `MvZpExtension.exists_totally_ramified`.

## Main results

* `MvZpExtension.inertiaSubgroup_inf_Xinf`: `I_w(L∞/K) ∩ X∞ = 1`, unconditionally.
* `MvZpExtension.exists_mem_Xinf_mul_mem_inertiaSubgroup`: `G = X∞ · I_w(L∞/K)` when `K∞/K` is
  totally ramified at the place below `w`.
* `MvZpExtension.xinfQuotientMulEquivOfPlace` and
  `MvZpExtension.xinfQuotientMulEquivOfPlace'`: **Step 1**, with `I` produced.
* `MvZpExtension.commutator_sup_iSup_inertiaSubgroup_le_fixingSubgroup_L0In`: the containment
  `L₀ ⊆ L∞^H` of the blueprint's `L₀ = L∞^H`.  The reverse containment needs the maximality of
  `L₀` and is not proved here.
-/

open IntermediateField

variable {p : ℕ} [Fact p.Prime] {ι K Kinf : Type*} [Finite ι]
variable [Field K] [NumberField K] [Field Kinf] [Algebra K Kinf] [IsGalois K Kinf]

namespace MvZpExtension

variable (H : MvZpExtension p ι K Kinf)

/-- `X∞` is the image of `Gal(L∞/K∞) → Gal(L∞/K)`. -/
theorem Xinf_eq_range :
    H.Xinf = (IntermediateField.restrictRestrictAlgEquivMapHom K
      ↥(H.Linf.restrictScalars K) ↥H.KinfIn ↥(H.Linf.restrictScalars K)).range :=
  (IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup' K H.KinfIn).symm

/-- `X∞` is the kernel of `G → Γ`. -/
theorem Xinf_eq_ker :
    H.Xinf = (AlgEquiv.restrictNormalHom (F := K)
      (K₁ := ↥(H.Linf.restrictScalars K)) ↥H.KinfIn).ker :=
  (IntermediateField.restrictNormalHom_ker H.KinfIn).symm

/-- **`I_w(L∞/K) ∩ X∞ = 1`**: the inertia subgroup of a place of `L∞` meets `X∞` trivially,
because `L∞ / K∞` is unramified.  This is the hypothesis `hIX` of
`MvZpExtension.xinfQuotientMulEquivOfInertia`. -/
theorem inertiaSubgroup_inf_Xinf (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ)
    (g : H.GG) (hI : g ∈ w.inertiaSubgroup K) (hX : g ∈ H.Xinf) : g = 1 := by
  rw [H.Xinf_eq_range] at hX
  obtain ⟨τ, rfl⟩ := hX
  have hτ : τ ∈ w.inertiaSubgroup ↥H.KinfIn := by
    rw [AbsoluteValue.inertiaSubgroup_eq_comap K ↥H.KinfIn]
    exact hI
  rw [H.inertiaSubgroup_KinfIn_eq_bot w, Subgroup.mem_bot] at hτ
  rw [hτ, map_one]

/-- **`G = X∞ · I_w(L∞/K)`** when `K∞ / K` is totally ramified at the place below `w`.  This is
the hypothesis `hG` of `MvZpExtension.xinfQuotientMulEquivOfInertia`. -/
theorem exists_mem_Xinf_mul_mem_inertiaSubgroup
    (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ) (v : AbsoluteValue Kinf ℝ)
    (hvw : w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective =
      v.comp (f := (H.kinfInEquiv : ↥H.KinfIn →+* Kinf)) H.kinfInEquiv.injective)
    (hram : v.inertiaSubgroup K = ⊤) (g : H.GG) :
    ∃ x ∈ H.Xinf, ∃ i ∈ w.inertiaSubgroup K, g = x * i := by
  have hbot : (w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective).inertiaSubgroup K
      = ⊤ := by
    rw [hvw, AbsoluteValue.inertiaSubgroup_comp_algEquiv_eq_comap, hram]
    exact Subgroup.comap_top _
  have hmap : (w.inertiaSubgroup K).map
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(H.Linf.restrictScalars K)) ↥H.KinfIn) = ⊤ := by
    rw [AbsoluteValue.map_inertiaSubgroup_eq_of_liesOver K
      (w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective) w]
    exact hbot
  have hg : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(H.Linf.restrictScalars K)) ↥H.KinfIn g ∈
      (w.inertiaSubgroup K).map (AlgEquiv.restrictNormalHom ↥H.KinfIn) := by
    rw [hmap]; trivial
  obtain ⟨i, hi, hgi⟩ := hg
  refine ⟨g * i⁻¹, ?_, i, hi, by group⟩
  rw [H.Xinf_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, hgi, mul_inv_cancel]

/-! ### All inertia subgroups of `G` lie in `Gal(L∞/L₀)` -/

/-- Every place of `K = K₀` is unramified in `K₀ / K`: `K₀ = ⊥`. -/
theorem isUnramifiedEverywhere_K_Kn_zero : NumberField.IsUnramifiedEverywhere K ↥(H.Kn 0) := by
  have hsub : Subsingleton Gal(↥(H.Kn 0)/K) := by
    rw [H.Kn_zero]
    exact (AlgEquiv.autCongr (IntermediateField.botEquiv K Kinf)).injective.subsingleton
  rw [NumberField.isUnramifiedEverywhere_iff]
  intro v _
  rw [AbsoluteValue.isUnramified_iff_inertiaSubgroup_eq_bot]
  exact le_bot_iff.1 fun σ _ ↦ by rw [Subgroup.mem_bot]; exact Subsingleton.elim _ _

/-- `L₀ / K` is unramified everywhere: `L₀ / K₀` is, and `K₀ = K`. -/
theorem isUnramifiedEverywhere_K_Ln_zero : NumberField.IsUnramifiedEverywhere K ↥(H.Ln 0) :=
  haveI := H.isUnramifiedEverywhere_K_Kn_zero
  NumberField.IsUnramifiedEverywhere.trans K ↥(H.Kn 0) ↥(H.Ln 0)

theorem Ln_zero_le_Linf :
    (H.Ln 0).restrictScalars K ≤ H.Linf.restrictScalars K := fun _ hx ↦ H.Ln_subset_Linf 0 hx

/-- `L₀`, viewed as an intermediate field of `L∞ / K`. -/
noncomputable def L0In : IntermediateField K ↥(H.Linf.restrictScalars K) :=
  IntermediateField.restrict H.Ln_zero_le_Linf

/-- The bridge `L₀ ≅ L₀In`. -/
noncomputable def l0InEquiv : ↥(H.Ln 0) ≃ₐ[K] ↥H.L0In :=
  (IntermediateField.restrictScalarsAlgEquiv K (H.Ln 0)).symm.trans
    (IntermediateField.restrict_algEquiv H.Ln_zero_le_Linf)

instance isGalois_K_L0In : IsGalois K ↥H.L0In :=
  H.l0InEquiv.transfer_galois.1 (H.isGalois_K_Ln 0)

instance normal_K_L0In : Normal K ↥H.L0In := IsGalois.to_normal

instance isUnramifiedEverywhere_K_L0In : NumberField.IsUnramifiedEverywhere K ↥H.L0In :=
  haveI := H.isUnramifiedEverywhere_K_Ln_zero
  NumberField.IsUnramifiedEverywhere.of_algEquiv H.l0InEquiv

/-- **Every inertia subgroup of `G = Gal(L∞/K)` lies in `Gal(L∞/L₀)`.**  This is the
containment `L₀ ⊆ L∞^H` of the claim `L₀ = L∞^H` in Step 1 of Washington's Lemma 13.15 (the
half that does not need the maximality of `L₀`), and it holds at *every* place, ramified or
not. -/
theorem inertiaSubgroup_le_fixingSubgroup_L0In
    (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ) :
    w.inertiaSubgroup K ≤ H.L0In.fixingSubgroup :=
  AbsoluteValue.inertiaSubgroup_le_fixingSubgroup K H.L0In w

/-- `K₀ = ⊥` also as an intermediate field of a `K₀`-extension. -/
theorem restrictScalars_bot_Kn_zero {M : Type*} [Field M] [Algebra K M] [Algebra ↥(H.Kn 0) M]
    [IsScalarTower K ↥(H.Kn 0) M] :
    ((⊥ : IntermediateField ↥(H.Kn 0) M).restrictScalars K) = ⊥ := by
  ext x
  simp only [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot, Set.mem_range]
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    rw [H.Kn_zero, IntermediateField.mem_bot] at hy
    obtain ⟨s, hs⟩ := hy
    exact ⟨s, by rw [IsScalarTower.algebraMap_apply K ↥(H.Kn 0) M]; congr 1; exact Subtype.ext hs⟩
  · rintro ⟨s, rfl⟩
    exact ⟨algebraMap K ↥(H.Kn 0) s, by rw [← IsScalarTower.algebraMap_apply]⟩

/-- `Gal(M/K₀) → Gal(M/K)` is bijective, because `K₀ = K`. -/
theorem bijective_restrictRestrict_Kn_zero {M : Type*} [Field M] [Algebra K M]
    [Algebra ↥(H.Kn 0) M] [IsScalarTower K ↥(H.Kn 0) M] [Normal K M] :
    Function.Bijective
      (IntermediateField.restrictRestrictAlgEquivMapHom K M ↥(H.Kn 0) M) := by
  refine ⟨IntermediateField.restrictRestrictAlgEquivMapHom_injective_of_tower_top K ↥(H.Kn 0) M,
    fun σ ↦ ?_⟩
  have hr : (IntermediateField.restrictRestrictAlgEquivMapHom K M ↥(H.Kn 0) M).range = ⊤ := by
    rw [IntermediateField.range_restrictRestrictAlgEquivMapHom_eq_fixingSubgroup,
      H.restrictScalars_bot_Kn_zero, IntermediateField.fixingSubgroup_bot]
  have : σ ∈ (IntermediateField.restrictRestrictAlgEquivMapHom K M ↥(H.Kn 0) M).range := by
    rw [hr]; trivial
  exact this

/-- `Gal(L₀/K)` is abelian: it is `Gal(L₀/K₀)`, and `L₀ / K₀` is abelian. -/
theorem mul_comm_gal_K_Ln_zero (σ τ : Gal(↥(H.Ln 0)/K)) : σ * τ = τ * σ := by
  obtain ⟨σ', rfl⟩ := (H.bijective_restrictRestrict_Kn_zero (M := ↥(H.Ln 0))).2 σ
  obtain ⟨τ', rfl⟩ := (H.bijective_restrictRestrict_Kn_zero (M := ↥(H.Ln 0))).2 τ
  rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm σ' τ']

/-- `Gal(L₀In/K)` is abelian. -/
theorem mul_comm_gal_K_L0In (σ τ : Gal(↥H.L0In/K)) : σ * τ = τ * σ := by
  apply (AlgEquiv.autCongr H.l0InEquiv).symm.injective
  rw [map_mul, map_mul]
  exact H.mul_comm_gal_K_Ln_zero _ _

/-- **The commutator subgroup of `G` lies in `Gal(L∞/L₀)`**, because `L₀ / K` is abelian. -/
theorem commutator_le_fixingSubgroup_L0In : commutator H.GG ≤ H.L0In.fixingSubgroup := by
  rw [← H.L0In.restrictNormalHom_ker, commutator_eq_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, b, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact H.mul_comm_gal_K_L0In _ _

/-- **`H ⊆ Gal(L∞/L₀)`**, where `H` is the subgroup of `G = Gal(L∞/K)` generated by the
commutator subgroup and by the inertia subgroups at *all* places of `L∞`.  This is the
containment `L₀ ⊆ L∞^H` of the claim `L₀ = L∞^H` in Step 1 of Washington's Lemma 13.15.  Since
`Gal(L∞/L₀)` is closed, the closure of that subgroup is contained in it as well. -/
theorem commutator_sup_iSup_inertiaSubgroup_le_fixingSubgroup_L0In :
    (commutator H.GG ⊔ ⨆ w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ,
      w.inertiaSubgroup K) ≤ H.L0In.fixingSubgroup :=
  sup_le H.commutator_le_fixingSubgroup_L0In
    (iSup_le fun w ↦ H.inertiaSubgroup_le_fixingSubgroup_L0In w)

/-! ### The place of `K∞` below a place of `L∞` -/

/-- The place of `K∞` below a place `w` of `L∞`, transported across `MvZpExtension.kinfInEquiv`
so that it lives on `K∞` itself rather than on `MvZpExtension.KinfIn`. -/
noncomputable def placeBelow (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ) :
    AbsoluteValue Kinf ℝ :=
  (w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective).comp
    (f := (H.kinfInEquiv.symm : Kinf →+* ↥H.KinfIn)) H.kinfInEquiv.symm.injective

theorem comp_placeBelow (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ) :
    w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective =
      (H.placeBelow w).comp (f := (H.kinfInEquiv : ↥H.KinfIn →+* Kinf))
        H.kinfInEquiv.injective :=
  AbsoluteValue.ext fun y ↦ congrArg (fun z ↦ w (algebraMap ↥H.KinfIn _ z))
    (H.kinfInEquiv.symm_apply_apply y).symm

/-- **Blueprint node `Xn-isom-qout-of-totally-ramified`, Step 1, with the inertia subgroup
produced.**  Let `w` be a place of `L∞` lying over a place `v` of `K∞` at which `K∞ / K` is
totally ramified, and let `Y ≤ X∞` contain `T X∞`.  Then `X∞ / Y ≅ G / (I_w Y)`. -/
noncomputable def xinfQuotientMulEquivOfPlace (γ : H.GG ⧸ H.Xinf)
    (hγ : Dense (Subgroup.zpowers γ : Set (H.GG ⧸ H.Xinf)))
    (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ) (v : AbsoluteValue Kinf ℝ)
    (hvw : w.comp (algebraMap ↥H.KinfIn ↥(H.Linf.restrictScalars K)).injective =
      v.comp (f := (H.kinfInEquiv : ↥H.KinfIn →+* Kinf)) H.kinfInEquiv.injective)
    (hram : v.inertiaSubgroup K = ⊤)
    (Y : Subgroup H.GG) (hYX : Y ≤ H.Xinf)
    (hTY : Subgroup.gammaSubOneG H.Xinf H.mul_comm_Xinf' γ ≤ Y) :
    letI : Y.Normal := Subgroup.normal_of_gammaSubOneG_le H.Xinf H.mul_comm_Xinf' γ
      H.isClosed_Xinf hγ hTY
    letI : (w.inertiaSubgroup K ⊔ Y).Normal :=
      Subgroup.normal_of_gammaSubOneG_le H.Xinf H.mul_comm_Xinf' γ H.isClosed_Xinf hγ
        (le_trans hTY (le_sup_right : Y ≤ w.inertiaSubgroup K ⊔ Y))
    (H.Xinf ⧸ Y.subgroupOf H.Xinf) ≃* (H.GG ⧸ (w.inertiaSubgroup K ⊔ Y)) :=
  H.xinfQuotientMulEquivOfInertia γ hγ (w.inertiaSubgroup K) Y hYX hTY
    (H.inertiaSubgroup_inf_Xinf w)
    (H.exists_mem_Xinf_mul_mem_inertiaSubgroup w v hvw hram)

/-- **Step 1**, in the form that only mentions the place `w` of `L∞`: if `K∞ / K` is totally
ramified at the place of `K∞` below `w`, then `X∞ / Y ≅ G / (I_w Y)`. -/
noncomputable def xinfQuotientMulEquivOfPlace' (γ : H.GG ⧸ H.Xinf)
    (hγ : Dense (Subgroup.zpowers γ : Set (H.GG ⧸ H.Xinf)))
    (w : AbsoluteValue ↥(H.Linf.restrictScalars K) ℝ)
    (hram : (H.placeBelow w).inertiaSubgroup K = ⊤)
    (Y : Subgroup H.GG) (hYX : Y ≤ H.Xinf)
    (hTY : Subgroup.gammaSubOneG H.Xinf H.mul_comm_Xinf' γ ≤ Y) :
    letI : Y.Normal := Subgroup.normal_of_gammaSubOneG_le H.Xinf H.mul_comm_Xinf' γ
      H.isClosed_Xinf hγ hTY
    letI : (w.inertiaSubgroup K ⊔ Y).Normal :=
      Subgroup.normal_of_gammaSubOneG_le H.Xinf H.mul_comm_Xinf' γ H.isClosed_Xinf hγ
        (le_trans hTY (le_sup_right : Y ≤ w.inertiaSubgroup K ⊔ Y))
    (H.Xinf ⧸ Y.subgroupOf H.Xinf) ≃* (H.GG ⧸ (w.inertiaSubgroup K ⊔ Y)) :=
  H.xinfQuotientMulEquivOfPlace γ hγ w (H.placeBelow w) (H.comp_placeBelow w) hram Y hYX hTY

end MvZpExtension
